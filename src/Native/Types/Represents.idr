||| What ordinary code holds the values of a type as (`Represents`, `Only`,
||| `ConOf`, `FieldOf`, `Immediate`): the representation contract between
||| the code generator, which lays values out, and the runtime's support
||| tier, which reads and makes them.
|||
||| Each constructor of these relations is a statement of the layout, and
||| the only place it is made: the support tier converts between a value
||| and an object, reads a field, or makes a value, only with the evidence
||| of one (`Native.Support.Obj` takes it), so that no code takes a value
||| for what it is not. A statement the code generator does not keep would
||| be a wrong layout, which the tests of the primitive that uses it find:
||| the statements are the trusted part, few and in one place.
|||
||| Part of the type layer, the modules of `Types`, which the code generator
||| and the runtime's support tier read.
module Native.Types.Represents

import Native.Types.ConstructorId
import Native.Types.Kind
import Native.Types.Struct

import Data.Buffer
import Native.Field

%default total

||| Every value of `a` is an object of kind `k`: a value of `a` can be taken
||| for one. A foreign pointer is not one of these, as it is of two kinds
||| (`Represents`).
public export
data Only : Kind -> Type -> Type where
  ||| A string is a `STRING` always, the empty one too.
  AString : Only Kind.STRING String
  ||| A list is a `CON` always: `[]` a static object of no fields.
  AList : Only Kind.CON (List a)
  ||| A buffer of `Data.Buffer` is a `BUFFER` always, the empty one too.
  ABuffer : Only Kind.BUFFER Buffer
  ||| A mutable record is a `STRUCT` always.
  AStruct : Only Kind.STRUCT (Struct fs)

||| An object of kind `k` is a value of `a`: one can be given as a value of
||| `a`.
public export
data Represents : Kind -> Type -> Type where
  ||| A kind that holds every value of a type holds values of it.
  Sole : Only k a -> Represents k a
  ||| A foreign pointer is an address outside the heap, as a `PTR`, the null
  ||| one too;
  AnAddress : Represents Kind.PTR (Ptr a)
  AnyAddress : Represents Kind.PTR AnyPtr
  ||| or, where `base` asks the runtime for a pointer to zero-ended bytes and
  ||| reads it only through the runtime, the string itself
  ||| (`Support.Ptr`), as an `AnyPtr` too, which `free` takes.
  AHeapString : Represents Kind.STRING (Ptr String)
  AnyHeapString : Represents Kind.STRING AnyPtr

||| Every value of `a` is an object whose header says its kind, or for a
||| type of `Handles` a handle: what a value of a type of several kinds is
||| read by (`Support.Obj.asKind`), which takes a handle for no object.
public export
data Objects : Type -> Type where
  ||| A type whose values are all objects of one kind.
  OfOne : Only k a -> Objects a
  ||| A foreign pointer, of either kind.
  Pointers : Objects (Ptr a)
  AnyPointers : Objects AnyPtr

||| A value of `a` may be a fixnum: a number the system tier gives for a
||| value of its own (`Native.System`), a handle, which the libraries hold
||| only to give back, as `base` holds a file as an `AnyPtr`. A foreign
||| pointer may be one, of either type, as the prelude turns one into the
||| other.
public export
data Handles : Type -> Type where
  AnyHandle : Handles AnyPtr
  AHandle : Handles (Ptr a)

||| The ids of `List`'s constructors, `[]` then `(::)`, as it declares them.
export
listNil, listCons : ConstructorId
listNil = ConstructorId.declared 0
listCons = ConstructorId.declared 1

||| Constructor `c` of the data type `t` is a `CON` of the id `c` and `n`
||| fields: a count no code computes with, only the statement's, as the
||| code generator's `ConH` has it. The ids are qualified in the constructors' types, here and
||| below: there a bare `listCons` would be a new variable, and the
||| statement one of every id.
public export
data ConOf : (t : Type) -> (c : ConstructorId) -> (n : Nat) -> Type where
  ListNil : ConOf (List a) Represents.listNil 0
  ListCons : ConOf (List a) Represents.listCons 2

||| `c` is a constructor of `t`, of some number of fields: what a view of a
||| value as one of its constructors asks.
public export
data IsCon : (t : Type) -> (c : ConstructorId) -> Type where
  HasArity : {0 n : Nat} -> ConOf t c n -> IsCon t c

||| Field `i` of constructor `c` of `t` holds a value of `f`.
public export
data FieldOf : (t : Type) -> (c : ConstructorId) -> (i : Bits64) -> (f : Type) -> Type where
  ConsHead : FieldOf (List a) Represents.listCons 0 a
  ConsTail : FieldOf (List a) Represents.listCons 1 (List a)

||| Ordinary code holds every value of `t` as a fixnum, the integer it
||| stands for: never an object.
public export
data Immediate : Type -> Type where
  ||| A character is its code point.
  AChar : Immediate Char
