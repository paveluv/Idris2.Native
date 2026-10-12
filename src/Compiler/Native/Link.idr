||| Linking: one static executable from the runtime seed
||| (`Compiler.Native.Seed`) and a program's rendered instructions and
||| read-only data, the per-thread areas sized as the program needs
||| (`Compiler.Native.Linkage`).
module Compiler.Native.Link

import public Compiler.Native.HeapObject
import Compiler.Native.Linkage
import Compiler.Native.Seed
import Compiler.Native.ELF
import public Compiler.Native.X86.Encode   -- linkProgram reports AsmProblem
import Compiler.Native.X86.Asm
import Compiler.Native.Bytes
import Data.List
import Data.Maybe
import Data.SortedMap

%default total

------------------------------------------------------------------------------
-- Linking: one image from the seed and a program

||| A static executable from the seed and the program's own instructions and
||| read-only data, with allocation windows of `window` bytes, a multiple of
||| 8, and the per-thread areas the program needs (`Areas`). The program
||| defines `symLabel SymMain`, which is entered with `k = HALT`, `hp`/`hplim`
||| set and the stack 16-aligned, and numbers its other labels from
||| `reservedLabels`. Each item of read-only data follows the seed's,
||| 8-aligned, at its label. Fails with what it could not assemble: labels it
||| could not resolve, and fields that do not fit.
export
linkProgram : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
              (window : Int) -> (areas : Areas) -> (program : List Instr) ->
              (rodata : List (Label, List Bits8)) -> Either (List AsmProblem) (List Bits8)
linkProgram enc window areas program items =
  let text = seedText enc window ++ program
      tl = layout textBase text
      ts = codeSize textBase text
      (seedData, rsyms) = seedRodata tl
      rodata = seedData ++ foldr (\(_, item), rest => pad8 item ++ rest) [] items
      offsets = offsetsFrom (cast (length seedData)) items
      as = maxAreas seedAreas areas
      lay = planLayout ts (cast (length rodata)) (seedBssSize as)
      env = fromList (map (\(s, off) => (symLabel s, rodataBase lay + off)) rsyms
                   ++ map (\(s, off) => (symLabel s, bssBase lay + off)) (seedBss as)
                   ++ map (\(l, off) => (l, rodataBase lay + off)) offsets)
      (bytes, labels, problems) = assembleWith env textBase text
      entry = fromMaybe textBase (lookup (symLabel SymStart) labels)
  in if null problems then Right (elfImage X86_64 lay bytes rodata (seedBssSize as) entry)
                      else Left problems
  where
    -- each item's label at its offset, the items laid end to end from `at`
    offsetsFrom : Int -> List (Label, List Bits8) -> List (Label, Int)
    offsetsFrom _ [] = []
    offsetsFrom at ((l, item) :: rest) = (l, at) :: offsetsFrom (at + cast (length (pad8 item))) rest

||| `linkProgram` for a program that uses no per-thread area beyond the
||| seed's, with no read-only data of its own.
export
linkWith : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
           (window : Int) -> (program : List Instr) -> Either (List AsmProblem) (List Bits8)
linkWith enc window program = linkProgram enc window seedAreas program []

||| `linkWith` the default window.
export
link : (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
       (program : List Instr) -> Either (List AsmProblem) (List Bits8)
link enc = linkWith enc windowBytes
