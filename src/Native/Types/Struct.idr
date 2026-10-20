||| Mutable records (`Struct`): an object of the heap of so many raw words
||| and then values of the types listed, each read and written in place,
||| which the collector walks by its header, scanning the values alone. A
||| record of Idris is a value, never written once made; a `Struct` is a
||| cell of several fields, as an `IORef` is a cell of one, for what is
||| rewritten as it is used: a file's offsets into its buffer, and the
||| buffer.
|||
||| A raw word is read and written by its index, below the number of raw
||| words (`Below`), and a value by its index, below the number of its
||| values, as a value of the type the list has there (`valueType`); so no
||| access is of a word or a value the record does not have, nor of another
||| type than it holds. A record is made value by value, its raw words zero
||| (`Support.StructObj`).
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is).
module Native.Types.Struct

%default total

||| A mutable record of `raws` raw words, then values of the types
||| `values`, as the kind `STRUCT` lays it out; at most 15 raw words, which
||| its header counts in four bits.
export
data Struct : (raws : Nat) -> (values : List Type) -> Type where [external]

||| The index is below the number.
public export
data Below : (index, n : Nat) -> Type where
  FirstBelow : Below Z (S n)
  NextBelow : Below i n -> Below (S i) (S n)

||| The type the list has at an index below its length.
public export
valueType : (values : List Type) -> Below index (length values) -> Type
valueType (a :: _) FirstBelow = a
valueType (_ :: as) (NextBelow b) = valueType as b

||| A count a record is made with, of its type's: the word is the number.
public export
data Sized : (count : Bits64) -> (n : Nat) -> Type where
  MkSized : Sized (cast n) n
