||| Mutable records (`Struct`): an object of the heap of named fields
||| (`Native.Field`), its raw words then its values, each read and written
||| in place, which the collector walks by its header, scanning the values
||| alone. A record of Idris is a value, never written once made; a
||| `Struct` is a cell of several fields, as an `IORef` is a cell of one, for
||| what is rewritten as it is used: a file's offsets into its buffer, and
||| the buffer.
|||
||| A field is read and written by its name, as the type its carrier says,
||| a raw word as its machine type or its address, a value as ordinary code
||| holds it; so no access is of a field the record does not have, nor of
||| another type than it holds. A record is made value by value, its raw
||| words zero (`Support.StructObj`).
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is).
module Native.Types.Struct

import Native.Field

%default total

||| A mutable record of the fields, as the kind `STRUCT` lays it out: its
||| raw words, at most 15, which its header counts in four bits, then its
||| values.
export
data Struct : (fields : List Field) -> Type where [external]
