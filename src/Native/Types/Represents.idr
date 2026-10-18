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

import Native.Types.Kind

%default total

||| Every value of `a` is an object of kind `k`: a value of `a` can be taken
||| for one.
public export
data Only : Kind -> Type -> Type where
  ||| A string is a `STRING` always, the empty one too.
  AString : Only STRING String
  ||| A list is a `CON` always: `[]` a static object of no fields.
  AList : Only CON (List a)
  ||| A foreign pointer is a `PTR`, the null one too.
  APointer : Only PTR (Ptr a)
  AnyPointer : Only PTR AnyPtr

||| An object of kind `k` is a value of `a`: one can be given as a value of
||| `a`.
public export
data Represents : Kind -> Type -> Type where
  ||| A kind that holds every value of a type holds values of it.
  Sole : Only k a -> Represents k a

||| Constructor `c` of the data type `t` is a `CON` of the id `c` and `n`
||| fields, by the order of `t`'s declaration.
public export
data ConOf : (t : Type) -> (c : Bits64) -> (n : Bits64) -> Type where
  ListNil : ConOf (List a) 0 0
  ListCons : ConOf (List a) 1 2

||| `c` is a constructor of `t`, of some number of fields: what a view of a
||| value as one of its constructors asks.
public export
data IsCon : (t : Type) -> (c : Bits64) -> Type where
  HasArity : {0 n : Bits64} -> ConOf t c n -> IsCon t c

||| Field `i` of constructor `c` of `t` holds a value of `f`.
public export
data FieldOf : (t : Type) -> (c : Bits64) -> (i : Bits64) -> (f : Type) -> Type where
  ConsHead : FieldOf (List a) 1 0 a
  ConsTail : FieldOf (List a) 1 1 (List a)

||| Ordinary code holds every value of `t` as a fixnum, the integer it
||| stands for: never an object.
public export
data Immediate : Type -> Type where
  ||| A character is its code point.
  AChar : Immediate Char
