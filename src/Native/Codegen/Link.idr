||| Linking: one static executable from the runtime seed
||| (`Native.Codegen.Seed`) and a program's rendered instructions and
||| read-only data, the per-thread areas sized as the program needs
||| (`Native.Codegen.Linkage.Areas`).
module Native.Codegen.Link

import Native.Codegen.ELF
import Native.Codegen.Linkage.Areas as Linkage
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.LittleEndian
import Native.Codegen.Platform
import Native.Codegen.Seed
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode

import Data.Maybe
import Data.SortedMap
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types

%default total

------------------------------------------------------------------------------
-- Linking: one image from the seed and a program

||| A static executable from the seed and the program's own instructions and
||| read-only data, with allocation windows of `window` bytes, a multiple of
||| 8, and the per-thread areas the program needs (`Areas`). The program
||| defines `label SymMain`, which is entered with `k = HALT`, `hp`/`hplim`
||| set and the stack 16-aligned, and numbers its other labels from
||| `reservedLabels`. Each item of read-only data follows the seed's,
||| 8-aligned, at its label. Fails with what it could not assemble: labels it
||| could not resolve, and fields that do not fit.
export
linkProgram : (enc : Types.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} ->
              (window : Int) -> (areas : Linkage.Areas) -> (program : List X86.Asm.Instr) ->
              (rodata : List (X86.Asm.Label, List Bits8)) ->
              Either (List X86.Encode.AsmProblem) ELF.Image
linkProgram enc window areas program items =
  let text = Seed.seedText enc window ++ program
      tl = X86.Encode.layout ELF.textBase text
      ts = X86.Encode.codeSize ELF.textBase text
      (seedData, rsyms) = Seed.seedRodata tl
      rodata = foldl (\b, (_, item) => b <>< LittleEndian.pad8 item) ([<] <>< seedData) items
      offsets = offsetsFrom (cast (length seedData)) items
      as = Linkage.Areas.maxAreas Seed.seedAreas areas
      lay = ELF.planLayout ts (LittleEndian.byteCount rodata) (Seed.seedBssSize as)
      env = fromList (map (\(s, off) => (Linkage.Sym.label s, rodataBase lay + off)) rsyms
                   ++ map (\(s, off) => (Linkage.Sym.label s, bssBase lay + off))
                     (Seed.seedBss as)
                   ++ map (\(l, off) => (l, rodataBase lay + off)) offsets)
      (bytes, labels, problems) = X86.Encode.assembleWith env ELF.textBase text
      entry = fromMaybe ELF.textBase (lookup (Linkage.Sym.label Linkage.Sym.SymStart) labels)
  in if null problems
    then Right (ELF.elfImage Platform.X86_64 lay bytes rodata (Seed.seedBssSize as) entry)
                      else Left problems
  where
    -- each item's label at its offset, the items laid end to end from `at`
    offsetsFrom : Int -> List (X86.Asm.Label, List Bits8) -> List (X86.Asm.Label, Int)
    offsetsFrom _ [] = []
    offsetsFrom at ((l, item) :: rest) = (l, at)
      :: offsetsFrom (at + cast (length (LittleEndian.pad8 item))) rest

||| The default allocation window: 4 MiB, the bytes the inline bump may
||| allocate before the runtime's slow path runs, which extends the window
||| or collects. A tiny window, chosen with `linkWith` or the directive
||| `nursery=`, makes tests take the slow path, and collect, often.
export
windowBytes : Int
windowBytes = 4 * 1024 * 1024

||| `linkProgram` for a program that uses no per-thread area beyond the
||| seed's, with no read-only data of its own.
export
linkWith : (enc : Types.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} ->
           (window : Int) -> (program : List X86.Asm.Instr) ->
           Either (List X86.Encode.AsmProblem) ELF.Image
linkWith enc window program = linkProgram enc window Seed.seedAreas program []

||| `linkWith` the default window.
export
link : (enc : Types.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} ->
       (program : List X86.Asm.Instr) -> Either (List X86.Encode.AsmProblem) ELF.Image
link enc = linkWith enc windowBytes
