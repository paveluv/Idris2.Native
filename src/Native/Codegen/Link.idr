||| Linking: one static executable from the runtime seed
||| (`Native.Codegen.Seed`) and a program's rendered instructions and
||| read-only data, the per-thread areas sized as the program needs
||| (`Native.Codegen.Linkage.Areas`).
module Native.Codegen.Link

import Native.Codegen.ByteSink
import Native.Codegen.ELF
import Native.Codegen.Linkage.Areas as Linkage
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.LittleEndian
import Native.Codegen.Platform
import Native.Codegen.Seed
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Datum as X86
import Native.Codegen.X86.Encode
import Native.Codegen.X86.LabelTable as X86

import Data.Maybe
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
||| `reservedLabels`, every label of its code and its data below `bound`.
||| Each item of read-only data follows the seed's, 8-aligned, at its
||| label. A word of the data that is a label's address is written once
||| the image is laid out, from the addresses the code is assembled with:
||| its own labels, as the assembler places them at the text's base, and
||| the data's, all in one table (`LabelTable`). Fails with what it could
||| not assemble: labels past the bound, labels it could not resolve, in
||| the code or in the data, and fields that do not fit, all found with
||| nothing encoded. The text and the data are encoded as the image is
||| written (`ELF.writeImage`), each instruction once, into the image's
||| buffer: no list of their bytes is made.
export
linkProgram : (enc : Types.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} ->
              (window : Int) -> (areas : Linkage.Areas) -> (bound : Nat) ->
              (program : List X86.Asm.Instr) -> (rodata : List (X86.Asm.Label, List X86.Datum)) ->
              IO (Either (List X86.Encode.AsmProblem) ELF.Image)
linkProgram enc window areas bound program items = do
  let text = Seed.seedText enc window ++ program
  labels <- X86.LabelTable.labelTable bound
  measured <- X86.Encode.measure labels ELF.textBase text
  let (seedData, rsyms) = Seed.seedRodata
      offsets = offsetsFrom (itemSize seedData) items
      as = Linkage.Areas.maxAreas Seed.seedAreas areas
      rodataSize = foldl (\n, (_, item) => n + itemSize item) (itemSize seedData) items
      lay = ELF.planLayout measured.size rodataSize (Seed.seedBssSize as)
      env = map (\(s, off) => (Linkage.Sym.label s, rodataBase lay + off)) rsyms
              ++ map (\(s, off) => (Linkage.Sym.label s, bssBase lay + off)) (Seed.seedBss as)
              ++ map (\(l, off) => (l, rodataBase lay + off)) offsets
      dataItems = seedData :: map snd items
  outside <- X86.Encode.defineEnvironment labels env
  problems <- X86.Encode.check labels measured ELF.textBase text
  unwritten <- missing labels [<] dataItems
  start <- X86.LabelTable.address labels (Linkage.Sym.label Linkage.Sym.SymStart)
  let code = ELF.written measured.size
               (\sink => X86.Encode.assembleInto sink labels measured ELF.textBase text)
      rodata = ELF.written rodataSize (\sink => placeAll sink labels dataItems)
      image = ELF.elfImage Platform.X86_64 lay code rodata (Seed.seedBssSize as)
                (fromMaybe ELF.textBase start)
  pure (if null outside && null problems && null unwritten then Right image
          else Left (outside ++ problems ++ unwritten))
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
    placeAll : ByteSink.Sink -> X86.LabelTable -> List (List X86.Datum) ->
               IO (Maybe ByteSink.Sink)
    placeAll sink labels [] = pure (Just sink)
    placeAll sink labels (item :: rest) = do
      Just s <- pieces sink item
        | Nothing => pure Nothing
      Just s' <- ByteSink.zeros s (cast (itemSize item - X86.Datum.size item))
        | Nothing => pure Nothing
      placeAll s' labels rest
      where
        -- a datum's bytes written
        piece : ByteSink.Sink -> X86.Datum -> IO (Maybe ByteSink.Sink)
        piece s d = case d of
          X86.Datum.Raw bs => ByteSink.put s bs
          X86.Datum.AddressOf l addend => do
            Just a <- X86.LabelTable.address labels l
              | Nothing => pure Nothing
            ByteSink.put s (X86.Datum.addressBytes a addend)

        -- each clause's action written out, `pure` or a `do` block, as
        -- `piece`'s case would not be: Idris then compiles the loop as a
        -- function of the world, not one that makes an action at each datum
        pieces : ByteSink.Sink -> List X86.Datum -> IO (Maybe ByteSink.Sink)
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
