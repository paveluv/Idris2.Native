-- The live table of Native.LiveTable, and the x86 slow path that reads it
-- (Native.Codegen.X86.AllocLive).
--
-- Generated code keeps every value of a function in a register, and every
-- register of ordinary code in a slot of SCRATCH, a per-thread area: in
--
--   pair : Nat -> List Nat -> (Nat, List Nat)
--   pair n xs = (n, n :: xs)
--
-- `n` and `xs` are in slots when `n :: xs` is allocated. An allocation
-- bumps the allocation pointer past the object; when that goes past the
-- window's limit, the site's slow path runs `idris_alloc_slow`, which may
-- collect and move objects. So the GC-visible values live across the
-- allocation (pointers to objects, like `xs`) go where the collector finds
-- and forwards them, ROOTS, and are reloaded from there after it. The raw
-- ones (a Bits64, a Double, a code address) need nothing: they stay in
-- their slots, which nothing the slow path runs writes, and the collector
-- never looks there.
--
-- Every site shares one routine for that. Its cold code is a call of the
-- routine, a jump back, and the site's live table: how many GC-visible
-- slots, then the slots, each entry 1, 2 or 4 bytes, the narrowest that
-- holds them all. The routine finds the table just past the jump its call
-- returns to.
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
roundTrip : List Nat -> String
roundTrip slots = case table slots of
  Nothing => "no table"
  Just (w, bytes) =>
    widthName w ++ ", " ++ show (length bytes) ++ " bytes, "
      ++ (if tableSlots w bytes == Just slots then "reads back" else "DOES NOT READ BACK")

-- the slots of `n` consecutive slots from `from`
run : (from, n : Nat) -> List Nat
run from n = take n [from ..]

cases : List (String, List Nat)
cases =
  [ ("nothing live", [])
  , ("slot 0", [0])
  , ("slots 3 and 5", [3, 5])
  , ("slot 255, the last of 8 bits", [255])
  , ("slot 256, the first past 8 bits", [256])
  , ("slot 65535, the last of 16 bits", [65535])
  , ("slots 1 and 65536, the first past 16 bits", [1, 65536])
  , ("255 slots, a count of 8 bits", run 0 255)
  , ("256 slots, a count past 8 bits", run 0 256)
  , ("slot 2^32, past every width", [4294967296]) ]

main : IO ()
main = do
  putStrLn "-- tables round-trip"
  traverse_ (\(name, c) => putStrLn (name ++ ": " ++ roundTrip c)) cases
  -- the format's bytes, little-endian: the count, then the slots
  putStrLn "-- bytes"
  putStrLn ("slots 3 and 5: " ++ show (map snd (table [3, 5])))
  putStrLn ("slot 300: " ++ show (map snd (table [300])))
  putStrLn ("slot 70000: " ++ show (map snd (table [70000])))
  -- bytes that are no table: a count larger than the slots that follow,
  -- a slot cut short
  putStrLn "-- not tables"
  putStrLn ("two counted, one given: " ++ show (tableSlots Sub8 [2, 9]))
  putStrLn ("a 16-bit slot cut short: " ++ show (tableSlots Sub16 [1, 0, 44]))
  -- a site's cold code: the call, the jump back to label 99, the table
  putStrLn "-- the stub"
  traverse_ (putStrLn . show) (stub 99 (Sub8, [2, 3, 5]))
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
