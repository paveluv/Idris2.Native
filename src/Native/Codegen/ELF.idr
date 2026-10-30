||| A minimal writer for static, non-PIE ELF64 executables, the only file the
||| native backend produces. No linker is involved: the backend lays out
||| text, read-only data and the zero-initialised areas itself, so every
||| address is known when the code is assembled. There is no writable data
||| section: statics are immutable and go in read-only data, and the
||| runtime's per-thread areas start zeroed, in bss. Position-independent
||| executables and shared objects are later work.
module Native.Codegen.ELF

import Native.Codegen.LittleEndian
import Native.Codegen.Platform

import Data.Buffer
import Native.Data.ByteSink as Data
import System.File.Buffer
import System.File.Error
import System.File.Permissions

%default total

||| Where the three loadable regions live, in the file and in memory. Each has
||| its own page-aligned segment: text (read, execute), rodata (read), bss
||| (read, write; occupies no file space).
public export
record Layout where
  constructor MkLayout
  textBase   : Int
  textOff    : Int
  rodataBase : Int
  rodataOff  : Int
  bssBase    : Int
  bssOff     : Int   -- where bss would sit in the file; keeps p_offset ≡ p_vaddr (mod page)

pageSize : Int
pageSize = 4096

||| Load address of the image; text begins one page in, after the headers.
export
imageBase : Int
imageBase = 0x400000

||| The text base does not depend on any size, so code can be assembled at it
||| before the data sizes are known.
export
textBase : Int
textBase = imageBase + pageSize

||| Fix the layout from the region sizes.
export
planLayout : (textSize : Int) -> (rodataSize : Int) -> (bssSize : Int) -> Layout
planLayout ts rs bs =
  let textOff   = pageSize
      rodataOff = LittleEndian.alignUp (textOff + ts) pageSize
      bssOff    = LittleEndian.alignUp (rodataOff + max rs 1) pageSize   -- always its own page
  in MkLayout (imageBase + textOff) textOff (imageBase + rodataOff) rodataOff (imageBase + bssOff)
    bssOff

-- ELF64 structures -------------------------------------------------------

||| A stretch of an image's bytes: bytes in order; a run of zero bytes; or
||| `size` bytes that a writer puts into the image when it is written,
||| through a sink over the stretch alone (`Native.Data.ByteSink`), so
||| that an image's text and read-only data are never made as lists of
||| their bytes. Abstract: an image is built, measured and written here,
||| and only passed along elsewhere.
export
data Stretch
  = Bytes (List Bits8)
  | Zeros Nat
  | Written Int (Data.ByteSink -> IO (Maybe Data.ByteSink))

||| A stretch of these bytes.
export
bytes : List Bits8 -> Stretch
bytes = Bytes

||| A stretch of `size` bytes that the writer puts into the image, through
||| a sink over them: it must write them all, and only them.
export
written : (size : Int) -> (Data.ByteSink -> IO (Maybe Data.ByteSink)) -> Stretch
written = Written

||| An image: its stretches, in file order.
public export
Image : Type
Image = List Stretch

||| The bytes a stretch takes.
export
stretchSize : Stretch -> Int
stretchSize (Bytes bs) = cast (length bs)
stretchSize (Zeros k) = cast k
stretchSize (Written k _) = k

||| The bytes an image takes.
export
imageSize : Image -> Int
imageSize image = sum (map stretchSize image)

||| The complete file image. `entry` is the virtual address of the first
||| instruction to run (normally `textBase` plus the offset of the startup
||| label). Section headers are not needed to run but let `readelf`/`objdump`
||| and debuggers see the regions.
export
elfImage : Platform.Arch -> Layout -> (text : Stretch) -> (rodata : Stretch) ->
           (bssSize : Int) ->
           (entry : Int) -> Image
elfImage m lay text rodata bssSize entry =
  let ts = stretchSize text
      rs = stretchSize rodata
      strOff = rodataOff lay + rs
      strSize = cast (length shstrtab)
      shoff = LittleEndian.alignUp (strOff + strSize) 8
      headers = elfHeader m entry shoff 3 5 4
             ++ programHeader (pfR + pfX) (textOff lay) (textBase lay) ts ts
             ++ programHeader pfR (rodataOff lay) (rodataBase lay) rs rs
             ++ programHeader (pfR + pfW) (bssOff lay) (bssBase lay) 0 bssSize
      sections = sectionHeader 0 shtNull 0 0 0 0 0
              ++ sectionHeader nameText shtProgbits (shfAlloc + shfExec) (textBase lay)
                (textOff lay) ts 16
              ++ sectionHeader nameRodata shtProgbits shfAlloc (rodataBase lay) (rodataOff lay) rs
                16
              ++ sectionHeader nameBss shtNobits (shfAlloc + shfWrite) (bssBase lay) (bssOff lay)
                bssSize 16
              ++ sectionHeader nameShstrtab shtStrtab 0 0 strOff strSize 1
  in [ Bytes headers
     , Zeros (cast (textOff lay - cast (length headers)))
     , text
     , Zeros (cast (rodataOff lay - (textOff lay + ts)))
     , rodata
     , Bytes shstrtab
     , Zeros (cast (shoff - (strOff + strSize)))
     , Bytes sections ]
  where
    pfX, pfW, pfR : Int
    pfX = 1
    pfW = 2
    pfR = 4

    shtNull, shtProgbits, shtStrtab, shtNobits : Int
    shtNull = 0
    shtProgbits = 1
    shtStrtab = 3
    shtNobits = 8

    shfWrite, shfAlloc, shfExec : Int
    shfWrite = 1
    shfAlloc = 2
    shfExec = 4

    u32 : Int -> List Bits8
    u32 = LittleEndian.le32

    u64 : Int -> List Bits8
    u64 = LittleEndian.le64 . cast

    elfHeader : Platform.Arch -> (entry : Int) -> (shoff : Int) -> (phnum : Int) -> (shnum : Int) ->
                (shstrndx : Int) ->
                List Bits8
    elfHeader m entry shoff phnum shnum shstrndx =
         [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0]
           ++ LittleEndian.zeros 8     -- magic, 64-bit, little-endian, version, SysV ABI
      ++ u16 2                                               -- ET_EXEC
      ++ u16 (machineCode m)
      ++ u32 1                                               -- EV_CURRENT
      ++ u64 entry
      ++ u64 ehsize                                    -- program headers follow the ELF header
      ++ u64 shoff
      ++ u32 0                                               -- flags
      ++ u16 ehsize ++ u16 phentsize ++ u16 phnum
      ++ u16 shentsize ++ u16 shnum ++ u16 shstrndx
      where
        ||| The ELF machine of an architecture.
        machineCode : Platform.Arch -> Int
        machineCode Platform.X86_64 = 0x3E
        machineCode Platform.AArch64 = 0xB7

        ehsize, phentsize, shentsize : Int
        ehsize = 64
        phentsize = 56
        shentsize = 64

        u16 : Int -> List Bits8
        u16 = LittleEndian.le16

    programHeader : (flags : Int) -> (off : Int) -> (vaddr : Int) -> (filesz : Int) ->
                    (memsz : Int) -> List Bits8
    programHeader flags off vaddr filesz memsz =
      u32 ptLoad ++ u32 flags ++ u64 off ++ u64 vaddr ++ u64 vaddr ++ u64 filesz ++ u64 memsz
        ++ u64 pageSize
      where
        ptLoad : Int
        ptLoad = 1

    sectionHeader : (name : Int) -> (ty : Int) -> (flags : Int) -> (addr : Int) -> (off : Int) ->
                    (size : Int) ->
                    (align : Int) -> List Bits8
    sectionHeader name ty flags addr off size align =
      u32 name ++ u32 ty ++ u64 flags ++ u64 addr ++ u64 off ++ u64 size ++ u32 0 ++ u32 0
        ++ u64 align ++ u64 0

    -- "\0.text\0.rodata\0.bss\0.shstrtab\0"
    shstrtab : List Bits8
    shstrtab = map (cast . ord) (unpack "\0.text\0.rodata\0.bss\0.shstrtab\0")

    nameText, nameRodata, nameBss, nameShstrtab : Int
    nameText = 1
    nameRodata = 7
    nameBss = 15
    nameShstrtab = 20

||| Why an image could not be written: the file, or a stretch whose writer
||| did not write exactly its bytes, at the stretch's offset in the image.
public export
data ImageError = Unwritable FileError | Miswritten Int

export
Show ImageError where
  show (Unwritable err) = show err
  show (Miswritten at) = "the stretch at " ++ show at ++ " of the image was not written as sized"

||| Write an image to a file and make it executable (owner rwx, others rx):
||| each stretch laid into one buffer where it falls, through a sink over
||| it alone. A stretch whose writer does not write exactly its bytes
||| leaves the file unwritten.
export
writeImage : (path : String) -> Image -> IO (Either ImageError ())
writeImage path image = do
  let n = imageSize image
  Just buf <- newBuffer n
    | Nothing => pure (Left (Unwritable FileWriteError))
  Right () <- write buf 0 image
    | Left err => pure (Left err)
  Right () <- writeBufferToFile path buf n
    | Left (err, _) => pure (Left (Unwritable err))
  Right () <- chmod path (MkPermissions [Read, Write, Execute] [Read, Execute] [Read, Execute])
    | Left err => pure (Left (Unwritable err))
  pure (Right ())
  where
    -- the stretch, at `at`, through a sink over it
    stretch : Buffer -> Int -> Stretch -> IO (Maybe Data.ByteSink)
    stretch buf at s = do
      Just sink <- Data.ByteSink.sink buf at (stretchSize s)
        | Nothing => pure Nothing
      case s of
        Bytes bs => Data.ByteSink.put sink bs
        Zeros z => Data.ByteSink.zeros sink z
        Written _ w => w sink

    write : Buffer -> Int -> Image -> IO (Either ImageError ())
    write buf at [] = pure (Right ())
    write buf at (s :: rest) = do
      Just sink <- stretch buf at s
        | Nothing => pure (Left (Miswritten at))
      if Data.ByteSink.full sink then write buf (at + stretchSize s) rest
        else pure (Left (Miswritten at))
