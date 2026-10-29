||| The encoder's three readings of an instruction agree, over every
||| instruction its other tests use: those of encode001's two groups,
||| which GNU as checks there, and those of encode002's sequences, whose
||| fields do not all fit. Nothing here needs binutils.
|||
||| The encoder gives an instruction's parts in Intel's instruction format
||| (`instrFormat pc rel i`, an `InstrFormat`), not its bytes, and they are
||| read three ways: the bytes it takes (`InstrFormat.size`, which
||| `instrSize` is, with no byte made), its bytes as a list
||| (`InstrFormat.bytes`, which `encodeRaw` is), and its bytes written
||| through a sink into a buffer, part by part (`InstrFormat.put`). The
||| assembler's first pass reads the sizes, the second writes the parts
||| into the image (`assembleInto`); `assemble`, the encoder's reference,
||| makes the bytes as a list.
module Agree

import Data.Buffer
import Data.List
import Data.SortedMap
import Data.String
import Groups
import Native.Codegen.ByteSink
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Codegen.X86.InstrFormat
import Native.Codegen.X86.LabelTable
import Native.Codegen.X86.OptionalByte
import Sequences

-- An instruction's parts, as Idris values. `mov rax, qword ptr [rbx+8]`
-- (`MovRM RAX (MBase RBX 8)`) is
--
--   Parts none (byte 0x48) OneByte 0x8B (byte 0x43) none Disp8 8 NoImm 0
--
-- no legacy prefix; the REX prefix 0x48, whose W bit makes the operand 64
-- bits wide; the opcode 0x8B of the one-byte map (mov r64, r/m64); the
-- ModRM byte 0x43, of mod 1 (a memory operand with an 8-bit
-- displacement), reg 0 (rax) and rm 3 (rbx); no SIB byte; the
-- displacement 8 in one byte; no immediate. Its size is 1 + 1 + 1 + 1 = 4
-- and its bytes are 48 8b 43 08. With r12 as the base, `mov rax, qword
-- ptr [r12+16]` needs the REX's B bit (0x49), since r12 is register 12, of
-- which the ModRM's rm holds the low three bits, 4; an rm of 4 means a SIB
-- byte follows, 0x24: scale 1, index 100, which is none, and base 100,
-- which with the REX's B bit is r12:
--
--   Parts none (byte 0x49) OneByte 0x8B (byte 0x44) (byte 0x24) Disp8 16 NoImm 0
--
-- five bytes, 49 8b 44 24 10. A branch `jne L3`, `L3` 16 bytes past the
-- branch's end, is
--
--   Parts none none TwoByte 0x85 none none NoDisp 0 Imm32 16
--
-- the opcode 0x85 of the two-byte map, which the escape byte 0x0f comes
-- before, and the offset 16 in four bytes where the immediate goes: 0f 85
-- 10 00 00 00. Each is checked against the encoder's bytes below.
examples : List (Instr, Int, InstrFormat)
examples =
  [ (MovRM RAX (MBase RBX 8), 0,
     Parts none (byte 0x48) OneByte 0x8B (byte 0x43) none Disp8 8 NoImm 0)
  , (MovRM RAX (MBase R12 16), 0,
     Parts none (byte 0x49) OneByte 0x8B (byte 0x44) (byte 0x24) Disp8 16 NoImm 0)
  , (Jcc NE 3, 16, Parts none none TwoByte 0x85 none none NoDisp 0 Imm32 16) ]

-- A byte as two hex digits.
hex : Bits8 -> String
hex b = pack [digit (b `div` 16), digit (b `mod` 16)]
  where
    digit : Bits8 -> Char
    digit d = if d < 10 then chr (ord '0' + cast d) else chr (ord 'a' + cast d - 10)

-- Every instruction of encode001's groups and of encode002's sequences.
corpus : List Instr
corpus = groupA ++ groupB ++ foldr (\(_, _, is), rest => is ++ rest) [] sequences

-- The addresses each instruction is read at: an alignment's padding is
-- what is left to its boundary, so `Align 8` takes 7 bytes at 1, 1 at 7
-- and none at 8.
addresses : List Int
addresses = [0, 1, 7, 8, 13]

-- The label-relative displacements each is read with, which a branch or a
-- RIP-relative operand holds in 32 bits and no other instruction reads:
-- 0 and -1; -2^31 and 2^31 - 1, the least and the greatest that fit; and
-- 2^32 + 5, which does not. Of one that does not fit, each reading takes
-- the low 32 bits, here 5: the list's bytes (`le32`) are 05 00 00 00, and
-- so are those written of the number cut to a `Bits32`
-- (`putBits32 (cast rel)`).
displacements : List Int
displacements = [0, -1, -2147483648, 2147483647, 4294967301]

-- The `n` bytes of the buffer from `at`.
bytesAt : Buffer -> (at : Int) -> (n : Nat) -> IO (List Bits8)
bytesAt buf at Z = pure []
bytesAt buf at (S k) = do
  b <- getBits8 buf at
  bs <- bytesAt buf (at + 1) k
  pure (b :: bs)

-- The first `n` bytes of the buffer set to 0xaa, which no write here
-- leaves where it does not write.
mark : Buffer -> (n : Nat) -> IO ()
mark buf Z = pure ()
mark buf (S k) = do setBits8 buf (cast k) 0xaa; mark buf k

-- Whether an instruction's readings agree at an address and a
-- displacement. Its parts written through a sink over exactly its size,
-- at offset 8 of a buffer of 32 bytes, fill the sink with `encodeRaw`'s
-- bytes, of which there are as many as its size says, and leave the bytes
-- either side of the sink as they were. Through a sink one byte short,
-- the writing gives no sink, and the byte past the sink's end is left as
-- it was: a part that would pass the end is not written.
agrees : Buffer -> Instr -> (pc, rel : Int) -> IO Bool
agrees buf i pc rel = do
  let expected = encodeRaw pc rel i
      n = instrSize pc i
  mark buf 32
  Just s <- ByteSink.sink buf 8 n
    | Nothing => pure False
  Just s' <- InstrFormat.put s (instrFormat pc rel i)
    | Nothing => pure False
  got <- bytesAt buf 8 (cast n)
  before <- getBits8 buf 7
  after <- getBits8 buf (8 + n)
  short <- if n == 0 then pure True else do
    mark buf 32
    Just t <- ByteSink.sink buf 8 (n - 1)
      | Nothing => pure False
    Nothing <- InstrFormat.put t (instrFormat pc rel i)
      | Just _ => pure False
    past <- getBits8 buf (8 + n - 1)
    pure (past == 0xaa)
  pure (cast (length expected) == n && ByteSink.full s' && got == expected && before == 0xaa
        && after == 0xaa && short)

-- Whether a sequence assembled at `base` into a buffer of the size its
-- first pass measures (`assembleInto`) is the bytes `assemble` makes. The
-- first pass puts the sequence's labels in a table of the labels below
-- 16, of which the sequences' are, apart from the one `assemble` makes.
assembledAgree : (base : Int) -> List Instr -> IO Bool
assembledAgree base is = do
  (code, _) <- assemble base is
  labels <- labelTable 16
  measured <- measure labels base is
  Just buf <- newBuffer measured.size
    | Nothing => pure False
  Just s <- ByteSink.sink buf 0 measured.size
    | Nothing => pure False
  Just s' <- assembleInto s labels measured base is
    | Nothing => pure False
  got <- bytesAt buf 0 (cast measured.size)
  pure (ByteSink.full s' && got == (code <>> []))

-- A sequence longer than the first table of sizes pass one makes, of
-- 65536 bytes, a size each, which grows as the pass goes, to 131072
-- bytes, then 262144: encode001's two groups five times, their labels
-- defined five times each, of which a reference takes the last
-- (`LabelTable.define`). `assemble` computes each size where it encodes
-- the instruction, and pass two reads them from the table.
long : List Instr
long = foldl (\acc, _ => acc <>< (groupA ++ groupB)) [<] [the Nat 1 .. 5] <>> []

-- A sink's checks of numbers near the largest `Int`, 2^63 - 1, in the
-- buffer of 32 bytes. The stretch of 5 bytes from 2^63 - 2 is not inside
-- it, though its end, 2^63 + 3, is an `Int` below 0 when summed, which is
-- not past 32: `sink` gives no sink. Through a sink over the 8 bytes from
-- 8, zeros of 2^63 - 1 do not fit, though 8 + (2^63 - 1) is an `Int`
-- below 8 when summed, and zeros of 2^64 + 4 do not, though the count
-- made an `Int` is 4, which fits: `zeros` gives no sink, and the bytes
-- from 8 are as `mark` left them. Zeros of 8 fill the stretch.
sinkEdges : Buffer -> IO ()
sinkEdges buf = do
  far <- ByteSink.sink buf 9223372036854775806 5
  putStrLn ("a stretch of 5 bytes from 2^63 - 2: " ++ given far)
  mark buf 32
  Just s <- ByteSink.sink buf 8 8
    | Nothing => putStrLn "no sink over the 8 bytes from 8"
  most <- ByteSink.zeros s 9223372036854775807
  wrapping <- ByteSink.zeros s 18446744073709551620
  left <- bytesAt buf 8 8
  putStrLn ("zeros of 2^63 - 1 into a stretch of 8: " ++ given most)
  putStrLn ("zeros of 2^64 + 4 into a stretch of 8: " ++ given wrapping
            ++ (if all (== 0xaa) left then ", nothing written" else ", WRITTEN"))
  Just t <- ByteSink.zeros s 8
    | Nothing => putStrLn "zeros of 8 into a stretch of 8: no sink"
  zs <- bytesAt buf 8 8
  putStrLn ("zeros of 8 into a stretch of 8: "
            ++ (if ByteSink.full t && all (== 0) zs then "the stretch filled" else "NOT filled"))
  where
    given : Maybe ByteSink.Sink -> String
    given (Just _) = "a sink"
    given Nothing = "no sink"

main : IO ()
main = do
  traverse_ (\(i, rel, parts) =>
               let bs = encodeRaw 0 rel i
                   same = InstrFormat.bytes parts == bs
               in putStrLn (show i ++ ": " ++ unwords (map hex bs)
                            ++ (if same then ", as its parts above" else ", NOT as above")))
    examples
  Just buf <- newBuffer 32
    | Nothing => putStrLn "no buffer"
  bad <- foldlM (\acc, (i, pc, rel) => do
             ok <- agrees buf i pc rel
             pure (if ok then acc else acc :< (i, pc, rel)))
           [<] [(i, pc, rel) | i <- corpus, pc <- addresses, rel <- displacements]
  putStrLn ("instructions: " ++ show (length corpus) ++ ", each at " ++ show (length addresses)
            ++ " addresses and " ++ show (length displacements) ++ " displacements")
  putStrLn ("readings that disagree: " ++ show (length (bad <>> [])))
  traverse_ (\(i, pc, rel) => putStrLn ("  " ++ show i ++ " at " ++ show pc ++ ", " ++ show rel))
    (take 5 (bad <>> []))
  let sequenced = [groupA, groupB] ++ map (\(_, _, is) => is) sequences
  same <- foldlM (\n, (base, is) => do
              ok <- assembledAgree base is
              pure (if ok then n + 1 else n))
            (the Nat 0) [(base, is) | base <- [0, 5], is <- sequenced]
  putStrLn ("sequences assembled into a buffer as assemble makes them: " ++ show same ++ " of "
            ++ show (2 * length sequenced))
  longSame <- assembledAgree 0 long
  putStrLn ("a sequence of " ++ show (length long)
            ++ " instructions assembled as assemble makes it: " ++ show longSame)
  sinkEdges buf
