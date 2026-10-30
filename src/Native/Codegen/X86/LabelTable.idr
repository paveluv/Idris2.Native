||| The addresses of an image's labels, by their numbers (`LabelTable`): a
||| word per label for its address and a byte for whether it has one, so
||| that defining a label and looking one up take no search and make no
||| object. The rendering numbers its labels from 0 up, the seed's first
||| (`Native.Codegen.Linkage.Sym`); the table grows to hold a label past
||| those it has (`holding`), as its two buffers grow
||| (`Native.Data.GrowingBuffer`).
|||
||| A label at or past the table's bound has no place, and is neither
||| defined nor found, and every access of the buffers is checked by
||| them: none lands outside them where Idris's Chez code is compiled
||| unsafe.
module Native.Codegen.X86.LabelTable

import Native.Codegen.X86.Asm

import Native.Data.GrowingBuffer as Data

%default total

||| The labels below its bound, each with an address or none. Abstract:
||| made by `labelTable` and `holding` alone.
export
record LabelTable where
  constructor MkLabelTable
  ||| The labels below it have a place.
  bound : Int
  ||| A byte per label: 1 once it has an address, else 0, as a new
  ||| buffer's room is.
  defined : Data.GrowingBuffer
  ||| A word per label: its address, once it has one.
  addresses : Data.GrowingBuffer

||| The table of its buffers: the labels below the bound both hold.
fromBuffers : Data.GrowingBuffer -> Data.GrowingBuffer -> LabelTable
fromBuffers d a =
  MkLabelTable (min (Data.GrowingBuffer.capacity d) (Data.GrowingBuffer.capacity a `div` 8)) d a

||| A table of the labels below `bound`, none with an address: of fewer, if
||| buffers that large cannot be made, which a size an `Int` does not
||| hold, wrapping, may be below 0.
export
labelTable : (bound : Nat) -> IO LabelTable
labelTable bound = do
  defined <- Data.GrowingBuffer.growingBuffer (cast bound)
  addresses <- Data.GrowingBuffer.growingBuffer (8 * cast bound)
  pure (fromBuffers defined addresses)

||| Whether the label has a place: its number below the bound, compared as
||| an `Integer`, before it is made an `Int`, which one past the largest
||| `Int` would wrap to a number that is.
placed : LabelTable -> Asm.Label -> Bool
placed t l = natToInteger l < cast t.bound

||| Whether a table can give the label a place: its number below the most
||| labels a table holds, 2^31, so that every place, and every word's
||| offset, is an `Int` far from wrapping. The number is compared as an
||| `Integer`, before it is made an `Int`, as `placed` compares it.
export
isPlaceable : Asm.Label -> Bool
isPlaceable l = natToInteger l < 2147483648

||| A table with a place for the label: this one, if it has one; else one
||| whose buffers have grown to hold it (`grownTo`), with every address it
||| holds, no label past the old bound defined; none for a label no table
||| can place (`isPlaceable`), or one whose buffers cannot be made.
export
holding : LabelTable -> Asm.Label -> IO (Maybe LabelTable)
holding t l =
  if placed t l then pure (Just t)
  else if not (isPlaceable l) then pure Nothing
  else grown (cast l + 1)
  where
    grown : Int -> IO (Maybe LabelTable)
    grown n = do
      Just defined <- Data.GrowingBuffer.grownTo t.defined n
        | Nothing => pure Nothing
      Just addresses <- Data.GrowingBuffer.grownTo t.addresses (8 * n)
        | Nothing => pure Nothing
      pure (Just (fromBuffers defined addresses))

||| The label at the address, if it has a place: whether it has. A label
||| defined twice takes the later address.
export
define : LabelTable -> Asm.Label -> (address : Int) -> IO Bool
define t l a = if placed t l then defineAt (cast l) else pure False
  where
    defineAt : Int -> IO Bool
    defineAt i = do
      Data.GrowingBuffer.setInt t.addresses (8 * i) a
      Data.GrowingBuffer.setBits8 t.defined i 1
      pure True

||| The label at the address, if it has a place and no address yet: whether
||| it has a place.
export
defineNew : LabelTable -> Asm.Label -> (address : Int) -> IO Bool
defineNew t l a = if placed t l then defineAt (cast l) else pure False
  where
    defineAt : Int -> IO Bool
    defineAt i = do
      d <- Data.GrowingBuffer.getBits8 t.defined i
      if d /= 0 then pure True else do
        Data.GrowingBuffer.setInt t.addresses (8 * i) a
        Data.GrowingBuffer.setBits8 t.defined i 1
        pure True

||| The label's address, if it has one.
export
address : LabelTable -> Asm.Label -> IO (Maybe Int)
address t l = if placed t l then addressAt (cast l) else pure Nothing
  where
    addressAt : Int -> IO (Maybe Int)
    addressAt i = do
      d <- Data.GrowingBuffer.getBits8 t.defined i
      if d == 0 then pure Nothing else do
        a <- Data.GrowingBuffer.getInt t.addresses (8 * i)
        pure (Just a)
