||| Tables (`Table`): functions of the integers from `lo` to `hi`, made once
||| as the words of their rows (`tabulate`), so that a call of one is a
||| read of its row (`index`). A table marked static
||| (`%cg native static`) is made when the native code generator compiles
||| the program, into its read-only data, and a read of it in flat code is
||| loads from the table's address, with no call. Unmarked, a table is a
||| constant as any other: made once where the code generator keeps
||| constants (`Bytes.generate` says which do), and read by the pure load
||| of each word (`Bytes.uncheckedWord`).
|||
||| This module is what a read's soundness rests on: `tabulate` is the
||| only maker of a table, so that a table's rows are always the words its
||| range and its row type say, and `index` reads them unchecked. It
||| trusts, besides, the implementation of `Row` it is given to be the one
||| `tabulate` was, as Idris's search finds one implementation for a type:
||| an implementation passed by name, of more words a row, could read past
||| the table.
module Native.Support.Table

import Native.Support.Table.Row

import Native.Types.Bytes as Types

%default total

||| The rows of a function of the integers from `lo` to `hi`, of values of
||| `r`: `hi - lo + 1` rows of `rowWords` words, one after the other, the
||| row of `lo` first, none if `hi` is below `lo`.
|||
||| A record of one field, which Idris erases, so that every code
||| generator holds a table as its `Bytes`, and flat code a static one as
||| its address. The range is in the type alone, never a field: a record
||| of two fields is no one value, so that flat code would read a static
||| one by calling the constant's flat form, which makes the table, and is
||| not flat. The constructor and the field are this module's alone.
export
record Table (lo, hi : Int) (r : Type) where
  constructor MkTable
  rows : Types.Bytes

||| The table of `meaning`: row `k` the row `meaning k`, for each `k` from
||| `lo` to `hi`, word `j` of it word `(k - lo) * rowWords + j` of the
||| rows; no rows for a `hi` below `lo`, however far below. The program
||| ends for a row type of no words, and for more words than an `Int`
||| counts, the count computed as an `Integer`, so that it never wraps
||| around to fewer words than the range asks; for more than fit in
||| memory, it ends by `generate`'s limit. Each word is made by a call of
||| `meaning`, so that a row of two words is computed twice.
|||
||| It ends the program by the crash primitive in place, as `generate`
||| does, so that Idris's Scheme backends keep the table it makes, and do
||| not make it again at each read (`generate` says why).
export
tabulate : Row r => {lo, hi : Int} -> (meaning : Int -> r) -> Table lo hi r
tabulate meaning =
  let w = Row.rowWords {r}
      count : Integer = max 0 ((cast hi - cast lo + 1) * cast w)
      n : Int = cast count
  in if w < 1 || cast n /= count
       -- lint: allow trust-escape: rows of no words, or more words than an `Int` counts, make no
       -- table, and ending the program is all there is to do
       then assert_total (prim__crash _ "idris: a table of rows of no words, or of too many words")
       else MkTable (Types.Bytes.generate n (\i => Row.word (meaning (lo + i `div` w)) (i `mod` w)))

||| Row `k` of the table, for `k` from `lo` to `hi`, as `inside` proves:
||| its words loaded, unchecked.
|||
||| It is inlined where it is used, where the range's `lo` and the row
||| type's words are constants, so that a read in flat code is the
||| table's address, the index `k * rowWords`, and one load for each word,
||| at a constant displacement where it fits one: `lo * rowWords` taken
||| off there, not from the index; for a `lo` too far from 0, it is added
||| to the index first. The rows, the index and that displacement are bound
||| before the function of the word number, whose body the flat
||| translation copies for each word, so that the field and the products
||| are computed once, not for each word.
|||
||| A word number outside the row, below 0 or from `rowWords`, gives 0,
||| never a load, so that an implementation of `Row` that asks for one
||| reads nothing outside its row: compared by the primitives, which the
||| flat translation computes for the constant word numbers of an inline
||| implementation, so that the bound is no instruction there. Ordinary
||| code compares at each word, in the function Idris makes of the case.
export %inline
index : Row r => {lo : Int} -> Table lo hi r -> (k : Int) ->
        (0 inside : (lo <= k && k <= hi) = True) -> r
index t k _ =
  let rows = t.rows
      i = k * Row.rowWords {r}
      first = negate lo * Row.rowWords {r}
  in Row.row (\j => case prim__lt_Int j (Row.rowWords {r}) of
                      0 => 0
                      _ => case prim__lt_Int j 0 of
                             -- lint: allow trust-escape: `tabulate`, the only maker, made
                             -- `(hi - lo + 1) * rowWords` words, by the implementation of `Row`
                             -- given here; `inside` puts `k` from `lo` to `hi`, and the tests put
                             -- `j` from 0 below `rowWords`, so word `(k - lo) * rowWords + j`
                             -- is one of them; and `i`, `first + j` and their sum, `Int`s that
                             -- wrap around, give that word exactly, as `uncheckedWord` sums
                             -- them: the sum is that word modulo 2^64, and an `Int`
                             0 => Types.Bytes.uncheckedWord rows i (first + j)
                             _ => 0)
