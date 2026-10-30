||| The fixups of a text (`FixupTable`), one for each reference to a label
||| in it, four words each in a buffer that grows
||| (`Native.Data.GrowingBuffer`): the offset in the text of the 32-bit
||| field the displacement to the label goes in, the offset of the end of
||| the instruction the field is in, the label's number and the constant
||| added to its address. A fixup is written and read as its words, so that
||| neither makes an object.
module Native.Codegen.X86.FixupTable

import Native.Codegen.X86.Asm

import Native.Data.GrowingBuffer as Data

%default total

||| The fixups, those of its buffer's rows that are filled. Abstract: made
||| by `fixupTable`, `holding` and `filledTo` alone.
export
record FixupTable where
  constructor MkFixupTable
  rows : Data.GrowingBuffer

||| The bytes of a fixup: its four words.
%inline
rowBytes : Int
rowBytes = 32

||| A table of no fixups, with room for some.
export
fixupTable : IO FixupTable
fixupTable = do
  rows <- Data.GrowingBuffer.growingBuffer 65536
  pure (MkFixupTable rows)

||| The fixups filled.
export
count : FixupTable -> Int
count t = Data.GrowingBuffer.used t.rows `div` rowBytes

||| Whether the table has room for `n` fixups.
export
hasRoom : FixupTable -> (n : Int) -> Bool
hasRoom t n = rowBytes * n <= Data.GrowingBuffer.capacity t.rows

||| The table with room for `n` fixups: this one, if it has it; else one
||| whose buffer has grown to (`grownTo`), with every fixup it holds; none
||| if its buffer cannot be made.
export
holding : FixupTable -> (n : Int) -> IO (Maybe FixupTable)
holding t n = do
  Just rows <- Data.GrowingBuffer.grownTo t.rows (rowBytes * n)
    | Nothing => pure Nothing
  pure (Just (MkFixupTable rows))

||| The table with its first `n` fixups filled.
export
filledTo : FixupTable -> (n : Int) -> FixupTable
filledTo t n = MkFixupTable (Data.GrowingBuffer.filledTo t.rows (rowBytes * n))

||| The `i`th fixup written, if the table has room for it (`hasRoom`): the
||| field's offset, the instruction's end, the label, one that a table of
||| labels can give a place (`LabelTable.isPlaceable`), whose number an
||| `Int` holds, and the constant.
export %inline
write : FixupTable -> (i, field, end : Int) -> Asm.Label -> (constant : Int) -> IO ()
write t i field end l d = writeRow t.rows (rowBytes * i) field end (cast l) d
  where
    -- A fixup's four words written at the offset of its row.
    writeRow : Data.GrowingBuffer -> (row, field, end, label, constant : Int) -> IO ()
    writeRow rows o field end l d = do
      Data.GrowingBuffer.setInt rows o field
      Data.GrowingBuffer.setInt rows (o + 8) end
      Data.GrowingBuffer.setInt rows (o + 16) l
      Data.GrowingBuffer.setInt rows (o + 24) d

||| A fixup's place in the table, read from the first fixup to the last.
||| Abstract: made by `first` and `next` alone; at run time the offset of
||| its row.
export
record Row where
  constructor MkRow
  offset : Int

||| The first fixup's place.
export %inline
first : Row
first = MkRow 0

||| The place of the fixup after the one at `r`.
export %inline
next : Row -> Row
next r = MkRow (r.offset + rowBytes)

||| The offset of the fixup's field.
export %inline
field : FixupTable -> Row -> IO Int
field t r = Data.GrowingBuffer.getInt t.rows r.offset

||| The offset of the end of the fixup's instruction.
export %inline
end : FixupTable -> Row -> IO Int
end t r = Data.GrowingBuffer.getInt t.rows (r.offset + 8)

||| The fixup's label.
export %inline
label : FixupTable -> Row -> IO Asm.Label
label t r = do
  n <- Data.GrowingBuffer.getInt t.rows (r.offset + 16)
  pure (cast n)

||| The constant added to the fixup's label.
export %inline
constant : FixupTable -> Row -> IO Int
constant t r = Data.GrowingBuffer.getInt t.rows (r.offset + 24)
