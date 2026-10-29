||| The addresses of an image's labels, by their numbers (`LabelTable`): a
||| word per label for its address and a byte for whether it has one, so
||| that defining a label and looking one up take no search and make no
||| object. The rendering numbers its labels from 0 up, the seed's first
||| (`Native.Codegen.Linkage.Sym`), so a table of the labels below a bound
||| it gives holds them all.
|||
||| Every access is checked against the table's bound, which the buffers
||| hold: a label at or past it has no place, and is neither defined nor
||| found, so no access lands outside the buffers where Idris's Chez code
||| is compiled unsafe.
module Native.Codegen.X86.LabelTable

import Native.Codegen.X86.Asm

import Data.Buffer

%default total

||| The labels below its bound, each with an address or none. Abstract:
||| made by `labelTable` alone.
export
record LabelTable where
  constructor MkLabelTable
  ||| The labels below it have a place.
  bound : Int
  ||| A byte per label: 1 once it has an address, else 0.
  defined : Buffer
  ||| A word per label: its address, once it has one.
  addresses : Buffer

||| A table of the labels below `bound`, none with an address: of fewer, if
||| buffers that large cannot be made.
export
labelTable : (bound : Nat) -> IO LabelTable
labelTable bound = do
  -- a new buffer is all zeros: no label is defined
  defined <- buffer (cast bound)
  addresses <- buffer (8 * cast bound)
  m <- rawSize defined
  n <- rawSize addresses
  pure (MkLabelTable (min m (n `div` 8)) defined addresses)
  where
    -- a buffer of the bytes, or an empty one: a size an `Int` does not
    -- hold wraps, and may be below 0
    buffer : Int -> IO Buffer
    buffer size = do
      Just b <- newBuffer size
        | Nothing => emptyBuffer
      pure b

||| Whether the label has a place: its number below the bound, compared as
||| an `Integer`, before it is made an `Int`, which one past the largest
||| `Int` would wrap to a number that is.
placed : LabelTable -> Asm.Label -> Bool
placed t l = natToInteger l < cast t.bound

||| The label at the address, if it has a place: whether it has. A label
||| defined twice takes the later address.
export
define : LabelTable -> Asm.Label -> (address : Int) -> IO Bool
define t l a = if placed t l then defineAt (cast l) else pure False
  where
    defineAt : Int -> IO Bool
    defineAt i = do
      setInt t.addresses (8 * i) a
      setBits8 t.defined i 1
      pure True

||| The label at the address, if it has a place and no address yet: whether
||| it has a place.
export
defineNew : LabelTable -> Asm.Label -> (address : Int) -> IO Bool
defineNew t l a = if placed t l then defineAt (cast l) else pure False
  where
    defineAt : Int -> IO Bool
    defineAt i = do
      d <- getBits8 t.defined i
      if d /= 0 then pure True else do
        setInt t.addresses (8 * i) a
        setBits8 t.defined i 1
        pure True

||| The label's address, if it has one.
export
address : LabelTable -> Asm.Label -> IO (Maybe Int)
address t l = if placed t l then addressAt (cast l) else pure Nothing
  where
    addressAt : Int -> IO (Maybe Int)
    addressAt i = do
      d <- getBits8 t.defined i
      if d == 0 then pure Nothing else map Just (getInt t.addresses (8 * i))
