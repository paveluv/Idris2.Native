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
-- never looks there. A value may be in a register instead: the slow path
-- of a site of a fixed size saves every word register in SAVE, the words
-- just before SCRATCH (the floating-point ones in FSAVE), and restores it
-- after, so a GC-visible one is listed by its word in SAVE, and a slot by
-- its word past them.
--
-- Every site shares one routine for that (one for sizes fixed when the
-- program is compiled, one for the rest). Its cold code is a call of the
-- routine, a jump back, and the site's live table: twice the number of
-- words listed, plus one if the floating-point registers are to be saved
-- too, then the words, each entry 1, 2 or 4 bytes, the narrowest that
-- holds them all. The routine finds the table just past the jump its call
-- returns to.
module Main

import Data.List
import Native.Codegen.Linkage.Sym
import Native.Codegen.X86.AllocLive
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.LiveTable
import Native.Width

widthName : SubWord -> String
widthName Sub8 = "8-bit"
widthName Sub16 = "16-bit"
widthName Sub32 = "32-bit"

-- the table, then reading it back gives the words it was made of
roundTrip : (Bool, List Nat) -> String
roundTrip (floats, words) = case table floats words of
  Nothing => "no table"
  Just (w, bytes) =>
    widthName w ++ ", " ++ show (length bytes) ++ " bytes, "
      ++ (if tableEntries w bytes == Just (floats, words) then "reads back"
            else "DOES NOT READ BACK")

-- the slots of `n` consecutive slots from `from`
run : (from, n : Nat) -> List Nat
run from n = take n [from ..]

cases : List (String, (Bool, List Nat))
cases =
  [ ("nothing live", (False, []))
  , ("the floating-point registers alone", (True, []))
  , ("word 0", (False, [0]))
  , ("words 3 and 15, and the floating-point registers", (True, [3, 15]))
  , ("word 255, the last of 8 bits", (False, [255]))
  , ("word 256, the first past 8 bits", (False, [256]))
  , ("word 65535, the last of 16 bits", (False, [65535]))
  , ("words 1 and 65536, the first past 16 bits", (False, [1, 65536]))
  , ("127 words, the most an 8-bit count holds", (True, run 0 127))
  , ("128 words, a count past 8 bits", (False, run 0 128))
  , ("word 2^32, past every width", (False, [4294967296])) ]

main : IO ()
main = do
  putStrLn "-- tables round-trip"
  traverse_ (\(name, c) => putStrLn (name ++ ": " ++ roundTrip c)) cases
  -- the format's bytes, little-endian: the count, then the words
  putStrLn "-- bytes"
  putStrLn ("words 3 and 15: " ++ show (map snd (table False [3, 15])))
  putStrLn ("the same, the floating-point registers too: " ++ show (map snd (table True [3, 15])))
  putStrLn ("word 300: " ++ show (map snd (table False [300])))
  putStrLn ("word 70000: " ++ show (map snd (table False [70000])))
  -- where a register and a slot are listed: a word register by its index
  -- in the target's description, a slot past them
  putStrLn ("word register 2: " ++ show (savedWord 2) ++ "; slot 0: " ++ show (slotWord 0)
            ++ "; slot 7: " ++ show (slotWord 7))
  -- bytes that are no table: a count larger than the slots that follow,
  -- a slot cut short
  putStrLn "-- not tables"
  putStrLn ("two counted, one given: " ++ show (tableEntries Sub8 [4, 9]))
  putStrLn ("a 16-bit word cut short: " ++ show (tableEntries Sub16 [2, 0, 44]))
  -- a site's cold code: the call, the jump back to label 99, the table
  putStrLn "-- the stub"
  traverse_ (putStrLn . show) (stub (SymAllocLive Sub8) 99 (Sub8, [4, 3, 15]))
  -- the table starts where the call returns to plus the jump's length,
  -- which every jump has
  putStrLn ("the table after the jump: " ++ show tableAt ++ " bytes")
  -- each routine's bytes, as the encoder lays them out from a 16-aligned
  -- start (the routine pads itself to one)
  putStrLn "-- the routines"
  traverse_ (\w => putStrLn (widthName w ++ ": " ++ show (size 0 (routine w 100))
                             ++ " bytes, sized " ++ show (size 0 (sizedRoutine w 100)) ++ " bytes"))
            [Sub8, Sub16, Sub32]
  -- the words of SAVE, before SCRATCH, x86-64's 11 word registers, and of
  -- FSAVE, its 16 floating-point registers
  putStrLn ("SAVE: " ++ show saveWords ++ " words, FSAVE: " ++ show floatSaveWords ++ " words")
  where
    size : Int -> List Instr -> Int
    size pc [] = pc
    size pc (i :: is) = size (pc + instrSize pc i) is
