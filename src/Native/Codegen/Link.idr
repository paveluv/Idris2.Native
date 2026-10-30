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
import Native.Codegen.X86.Assembler as X86
import Native.Codegen.X86.Datum as X86
import Native.Codegen.X86.Encode
import Native.Codegen.X86.LabelTable as X86

import Data.Maybe
import Native.Data.ByteSink as Data
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
||| `reservedLabels`, its labels' table made for those below `bound` to
||| begin with, and growing. Each item of read-only data follows the
||| seed's, 8-aligned, at its label. The seed's text and the program's are
||| encoded at their addresses, each instruction once, by an assembler
||| (`Native.Codegen.X86.Assembler`), into a buffer the image's text is
||| copied from; a word of the data that is a label's address is written
||| once the image is laid out, from the labels' addresses, the code's and
||| the data's, all in one table (`LabelTable`). Fails with what it could
||| not assemble: a field that does not fit, a label with no place, a
||| label it could not resolve, in the code or in the data, a displacement
||| too far.
export
linkProgram : (enc : Types.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} ->
              (window : Int) -> (areas : Linkage.Areas) -> (bound : Nat) ->
              (program : List X86.Asm.Instr) -> (rodata : List (X86.Asm.Label, List X86.Datum)) ->
              IO (Either (List X86.Encode.AsmProblem) ELF.Image)
linkProgram enc window areas bound program items = do
  asm <- X86.Assembler.assembler ELF.textBase bound
  X86.Assembler.encode asm (Seed.seedText enc window)
  X86.Assembler.encode asm program
  textSize <- X86.Assembler.size asm
  let (seedData, rsyms) = Seed.seedRodata
      offsets = offsetsFrom (itemSize seedData) items
      as = Linkage.Areas.maxAreas Seed.seedAreas areas
      rodataSize = foldl (\n, (_, item) => n + itemSize item) (itemSize seedData) items
      lay = ELF.planLayout textSize rodataSize (Seed.seedBssSize as)
      env = map (\(s, off) => (Linkage.Sym.label s, rodataBase lay + off)) rsyms
              ++ map (\(s, off) => (Linkage.Sym.label s, bssBase lay + off)) (Seed.seedBss as)
              ++ map (\(l, off) => (l, rodataBase lay + off)) offsets
      dataItems = seedData :: map snd items
  problems <- X86.Assembler.resolve asm env
  labels <- X86.Assembler.labels asm
  unwritten <- missing labels [<] dataItems
  start <- X86.LabelTable.address labels (Linkage.Sym.label Linkage.Sym.SymStart)
  let code = ELF.written textSize (X86.Assembler.put asm)
      rodata = ELF.written rodataSize (\sink => placeAll sink labels dataItems)
      image = ELF.elfImage Platform.X86_64 lay code rodata (Seed.seedBssSize as)
                (fromMaybe ELF.textBase start)
  pure (if null problems && null unwritten then Right image else Left (problems ++ unwritten))
  where
    -- the bytes an item takes, padded to a multiple of 8
    itemSize : List X86.Datum -> Int
    itemSize item = LittleEndian.alignUp (X86.Datum.size item) 8

    -- each item's label at its offset, the items laid end to end from `at`
    offsetsFrom : Int -> List (X86.Asm.Label, List X86.Datum) -> List (X86.Asm.Label, Int)
    offsetsFrom _ [] = []
    offsetsFrom at ((l, item) :: rest) = (l, at) :: offsetsFrom (at + itemSize item) rest

    -- the labels the items name that have no address in the table
    missing : X86.LabelTable -> SnocList X86.Encode.AsmProblem ->
              List (List X86.Datum) -> IO (List X86.Encode.AsmProblem)
    missing labels found [] = pure (found <>> [])
    missing labels found (item :: rest) = do
      found' <- named found item
      missing labels found' rest
      where
        named : SnocList X86.Encode.AsmProblem -> List X86.Datum ->
                IO (SnocList X86.Encode.AsmProblem)
        named found [] = pure found
        named found (X86.Datum.Raw _ :: ds) = named found ds
        named found (X86.Datum.AddressOf l _ :: ds) = do
          a <- X86.LabelTable.address labels l
          named (if isJust a then found else found :< X86.Encode.MissingLabel l) ds

    -- the items written end to end, each padded, each address read from the
    -- labels' table; a label that is not there, which the link refuses
    -- first, stops the writing with no sink
    placeAll : Data.ByteSink -> X86.LabelTable -> List (List X86.Datum) ->
               IO (Maybe Data.ByteSink)
    placeAll sink labels [] = pure (Just sink)
    placeAll sink labels (item :: rest) = do
      Just s <- pieces sink item
        | Nothing => pure Nothing
      Just s' <- Data.ByteSink.zeros s (cast (itemSize item - X86.Datum.size item))
        | Nothing => pure Nothing
      placeAll s' labels rest
      where
        -- a datum's bytes written
        piece : Data.ByteSink -> X86.Datum -> IO (Maybe Data.ByteSink)
        piece s d = case d of
          X86.Datum.Raw bs => Data.ByteSink.put s bs
          X86.Datum.AddressOf l addend => do
            Just a <- X86.LabelTable.address labels l
              | Nothing => pure Nothing
            Data.ByteSink.put s (X86.Datum.addressBytes a addend)

        -- each clause's action written out, `pure` or a `do` block, as
        -- `piece`'s case would not be: Idris then compiles the loop as a
        -- function of the world, not one that makes an action at each datum
        pieces : Data.ByteSink -> List X86.Datum -> IO (Maybe Data.ByteSink)
        pieces s [] = pure (Just s)
        pieces s (d :: ds) = do
          Just s' <- piece s d
            | Nothing => pure Nothing
          pieces s' ds

||| The default allocation window: 4 MiB, the bytes the inline bump may
||| allocate before the runtime's slow path runs, which extends the window
||| or collects. A tiny window, chosen with `linkProgram` or the directive
||| `nursery=`, makes tests take the slow path, and collect, often.
export
windowBytes : Int
windowBytes = 4 * 1024 * 1024
