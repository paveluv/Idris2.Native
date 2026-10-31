-- The live table of Native.LiveTable, and the x86 slow path that reads it
-- (Native.Codegen.X86.AllocLive).
--
-- Generated code keeps every value of a function in a register, and every
-- register in a slot of SCRATCH, a per-thread area: in
--
--   pair : Nat -> List Nat -> (Nat, List Nat)
--   pair n xs = (n, n :: xs)
--
-- `n` and `xs` are in slots when `n :: xs` is allocated. An allocation
-- bumps the allocation pointer past the object; when that goes past the
-- window's limit, the site's slow path runs `idris_alloc_slow`, which may
-- collect and move objects, and which, being runtime code with registers
-- of its own in SCRATCH, overwrites the slots. So whatever is live across
-- the allocation must be saved first and reloaded after: the GC-visible
-- values (pointers to objects, like `xs`) in ROOTS, where the collector
-- forwards them, and the raw ones (a Bits64, a Double, a code address)
-- where the collector never looks.
--
-- Every site shares one routine for that. Its cold code is a call of the
-- routine, a jump back, and the site's live table: how many GC-visible
-- slots, how many raw ones, then the slots, each entry 1, 2 or 4 bytes,
-- the narrowest that holds them all. The routine finds the table just past
-- the jump its call returns to.
module Main

import Data.List
import Native.Codegen.X86.AllocLive
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.LiveTable
import Native.Width

widthName : SubWord -> String
widthName Sub8 = "8-bit"
widthName Sub16 = "16-bit"
widthName Sub32 = "32-bit"

-- the table, then reading it back gives the slots it was made of
roundTrip : (List Nat, List Nat) -> String
roundTrip (gc, raw) = case table gc raw of
  Nothing => "no table"
  Just (w, bytes) =>
    widthName w ++ ", " ++ show (length bytes) ++ " bytes, "
      ++ (if tableSlots w bytes == Just (gc, raw) then "reads back" else "DOES NOT READ BACK")

-- the slots of `n` consecutive slots from `from`
run : (from, n : Nat) -> List Nat
run from n = take n [from ..]

cases : List (String, (List Nat, List Nat))
cases =
  [ ("nothing live", ([], []))
  , ("one raw slot, slot 0", ([], [0]))
  , ("slots 3 and 5 GC-visible, 7 raw", ([3, 5], [7]))
  , ("slot 255, the last of 8 bits", ([255], []))
  , ("slot 256, the first past 8 bits", ([256], []))
  , ("slot 65535, the last of 16 bits", ([], [65535]))
  , ("slot 65536, the first past 16 bits", ([65536], [1]))
  , ("255 GC-visible slots, a count of 8 bits", (run 0 255, []))
  , ("256 GC-visible slots, a count past 8 bits", (run 0 256, []))
  , ("slot 2^32, past every width", ([4294967296], [])) ]

main : IO ()
main = do
  putStrLn "-- tables round-trip"
  traverse_ (\(name, c) => putStrLn (name ++ ": " ++ roundTrip c)) cases
  -- the format's bytes, little-endian: counts, then the GC-visible slots,
  -- then the raw ones
  putStrLn "-- bytes"
  putStrLn ("slots 3 and 5 GC-visible, 7 raw: " ++ show (map snd (table [3, 5] [7])))
  putStrLn ("slot 300 GC-visible: " ++ show (map snd (table [300] [])))
  putStrLn ("raw slot 70000: " ++ show (map snd (table [] [70000])))
  -- bytes that are no table: a count larger than the slots that follow,
  -- a slot cut short
  putStrLn "-- not tables"
  putStrLn ("two GC-visible counted, one given: " ++ show (tableSlots Sub8 [2, 0, 9]))
  putStrLn ("a 16-bit slot cut short: " ++ show (tableSlots Sub16 [1, 0, 0, 0, 44]))
  -- a site's cold code: the call, the jump back to label 99, the table
  putStrLn "-- the stub"
  traverse_ (putStrLn . show) (stub 99 (Sub8, [2, 1, 3, 5, 7]))
  -- the table starts where the call returns to plus the jump's length,
  -- which every jump has
  putStrLn ("the table after the jump: " ++ show tableAt ++ " bytes")
  -- each routine's bytes, as the encoder lays them out from a 16-aligned
  -- start (the routine pads itself to one)
  putStrLn "-- the routines"
  traverse_ (\w => putStrLn (widthName w ++ ": " ++ show (size 0 (routine w 100)) ++ " bytes"))
            [Sub8, Sub16, Sub32]
  where
    size : Int -> List Instr -> Int
    size pc [] = pc
    size pc (i :: is) = size (pc + instrSize pc i) is
