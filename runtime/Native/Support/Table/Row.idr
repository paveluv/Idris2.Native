||| The rows of a table as words (`Row`): how many words a row of a type
||| is, each word of a row, and the row of its words, which a table
||| (`Native.Support.Table`) lays out one row after another and reads back.
module Native.Support.Table.Row

import Native.Primitive.DoubleBits

%default total

||| A type whose values are a table's rows, laid out as words.
|||
||| Each implementation is `%inline`, as those below are, so that its
||| methods' bodies unfold where a table is read. Without it, Idris unfolds
||| a method's body only where it finds the body simple, which `row`'s is
||| not, so that a read calls `row` and is given the implementation, a
||| record of functions. Flat code that reads such a table is then
||| refused, a function being no flat value; ordinary code calls a copy of
||| `row` at each read, `rowWords` a constant there only while the
||| implementation is `public export`. Idris parses `%inline` on an
||| implementation, which gives it to each of its methods, and on no
||| single method.
public export
interface Row r where
  ||| The words of a row, one at least.
  rowWords : Int
  ||| Word `j` of the row, for `j` from 0 below `rowWords`.
  word : r -> (j : Int) -> Bits64
  ||| The row of the words `w 0`, ..., `w (rowWords - 1)`, so that the row
  ||| of `word x` is `x`.
  row : (w : Int -> Bits64) -> r

||| A word is a row of one word, itself.
public export %inline
Row Bits64 where
  rowWords = 1
  word x _ = x
  row w = w 0

||| A double is a row of one word, its bits as IEEE 754 lays them out.
public export %inline
Row Double where
  rowWords = 1
  word x _ = Primitive.DoubleBits.doubleBits x
  row w = Primitive.DoubleBits.bitsDouble (w 0)

||| Two words are a row of two, the first one first.
public export %inline
Row (Bits64, Bits64) where
  rowWords = 2
  word (h, l) j = if j == 0 then h else l
  row w = (w 0, w 1)
