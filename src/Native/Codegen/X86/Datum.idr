||| The pieces of an image's read-only data (`Datum`): bytes as they are,
||| or a word that is the address of a label, which only the link knows.
|||
||| A static that holds another static's address, or a function's, is laid
||| out before anything is placed: the rendering names the label, and the
||| link writes the word once the image is laid out, from the labels of
||| its code and its data. An address is a word whatever the label, so the
||| data's size, and with it the image's layout, is known before any label
||| is placed.
module Native.Codegen.X86.Datum

import Native.Codegen.X86.Asm

import Data.SortedMap
import Native.Codegen.LittleEndian

%default total

||| A piece of read-only data.
public export
data Datum
  = ||| Bytes, as they are.
    Raw (List Bits8)
  | ||| The address of the label plus the addend, as a little-endian word.
    AddressOf Asm.Label Int

||| The bytes the pieces take, which no label decides.
export
size : List Datum -> Int
size = foldl (\n, d => n + datumSize d) 0
  where
    datumSize : Datum -> Int
    datumSize (Raw bs) = cast (length bs)
    datumSize (AddressOf _ _) = 8

||| The bytes of a piece, given the address of every label of the image:
||| the label, if the piece names one that has none.
export
bytes : SortedMap Asm.Label Int -> Datum -> Either Asm.Label (List Bits8)
bytes _ (Raw bs) = Right bs
bytes labels (AddressOf l addend) = case lookup l labels of
  Just a => Right (LittleEndian.le64 (cast (a + addend)))
  Nothing => Left l
