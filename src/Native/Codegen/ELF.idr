||| A minimal writer for static, non-PIE ELF64 executables, the only file the
||| native backend produces. No linker is involved: the backend lays out
||| text, read-only data and the zero-initialised areas itself, so every
||| address is known when the code is assembled. There is no writable data
||| section: statics are immutable and go in read-only data, and the
||| runtime's per-thread areas start zeroed, in bss. Position-independent
||| executables and shared objects are later work.
module Native.Codegen.ELF

import Native.Codegen.Bytes
import Native.Codegen.Platform

import Data.Buffer
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
      rodataOff = Bytes.alignUp (textOff + ts) pageSize
      bssOff    = Bytes.alignUp (rodataOff + max rs 1) pageSize   -- always its own page
  in MkLayout (imageBase + textOff) textOff (imageBase + rodataOff) rodataOff (imageBase + bssOff)
    bssOff

-- ELF64 structures -------------------------------------------------------

||| A stretch of an image's bytes: bytes in order; bytes accumulated at the
||| end of a snoc-list, the text the encoder made and the read-only data,
||| which the writer lays from their last byte, never read out into a list;
||| or a run of zero bytes. Abstract: an image is built, measured and
||| written here, and only passed along elsewhere.
export
data Stretch = Bytes (List Bits8) | SnocBytes (SnocList Bits8) | Zeros Nat

||| An image: its stretches, in file order.
public export
Image : Type
Image = List Stretch

||| The bytes a stretch takes.
export
stretchSize : Stretch -> Int
stretchSize (Bytes bs) = cast (length bs)
stretchSize (SnocBytes sx) = Bytes.byteCount sx
stretchSize (Zeros k) = cast k

||| The bytes an image takes.
export
imageSize : Image -> Int
imageSize image = sum (map stretchSize image)

||| The complete file image. `entry` is the virtual address of the first
||| instruction to run (normally `textBase` plus the offset of the startup
||| label). Section headers are not needed to run but let `readelf`/`objdump`
||| and debuggers see the regions.
export
elfImage : Platform.Arch -> Layout -> (text : SnocList Bits8) -> (rodata : SnocList Bits8) ->
           (bssSize : Int) ->
           (entry : Int) -> Image
elfImage m lay text rodata bssSize entry =
  let ts = Bytes.byteCount text
      rs = Bytes.byteCount rodata
      strOff = rodataOff lay + rs
      strSize = cast (length shstrtab)
      shoff = Bytes.alignUp (strOff + strSize) 8
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
     , SnocBytes text
     , Zeros (cast (rodataOff lay - (textOff lay + ts)))
     , SnocBytes rodata
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
    u32 = Bytes.le32

    u64 : Int -> List Bits8
    u64 = Bytes.le64 . cast

    elfHeader : Platform.Arch -> (entry : Int) -> (shoff : Int) -> (phnum : Int) -> (shnum : Int) ->
                (shstrndx : Int) ->
                List Bits8
    elfHeader m entry shoff phnum shnum shstrndx =
         [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0]
           ++ Bytes.zeros 8     -- magic, 64-bit, little-endian, version, SysV ABI
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
        u16 = Bytes.le16

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

||| Write an image to a file and make it executable (owner rwx, others rx):
||| each stretch laid into one buffer where it falls.
export
writeImage : (path : String) -> Image -> IO (Either FileError ())
writeImage path image = do
  let sized = map (\s => (s, stretchSize s)) image
      n = sum (map (\(_, k) => k) sized)
  Just buf <- newBuffer n
    | Nothing => pure (Left FileWriteError)
  write buf 0 sized
  Right () <- writeBufferToFile path buf n
    | Left (err, _) => pure (Left err)
  chmod path (MkPermissions [Read, Write, Execute] [Read, Execute] [Read, Execute])
  where
    front : Buffer -> Int -> List Bits8 -> IO ()
    front buf i [] = pure ()
    front buf i (b :: bs) = do setBits8 buf i b; front buf (i + 1) bs

    -- a snoc-list's bytes, its last at `i`, laid towards the front
    back : Buffer -> Int -> SnocList Bits8 -> IO ()
    back buf i [<] = pure ()
    back buf i (sx :< b) = do setBits8 buf i b; back buf (i - 1) sx

    blank : Buffer -> Int -> Nat -> IO ()
    blank buf i Z = pure ()
    blank buf i (S k) = do setBits8 buf i 0; blank buf (i + 1) k

    write : Buffer -> Int -> List (Stretch, Int) -> IO ()
    write buf at [] = pure ()
    write buf at ((s, k) :: rest) = do
      case s of
        Bytes bs => front buf at bs
        SnocBytes sx => back buf (at + k - 1) sx
        Zeros z => blank buf at z
      write buf (at + k) rest
