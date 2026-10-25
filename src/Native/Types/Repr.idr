||| What ordinary code holds the values of a type as (`Only`, `Repr`,
||| `Objects`, `Handles`, `ConOf`, `FieldOf`, `Fixnums`, `Immediate`), and
||| whether they change once made (`Immutable`): the representation
||| contract between the code generator, which lays values out, and the
||| runtime's support tier, which reads and makes them.
|||
||| Each relation is an interface with no methods, and each of its
||| implementations a statement; evidence is made only by searching for
||| one, never by the interface's constructor, which the linter refuses
||| (`forged-instance`). The layout relations are what the support tier's
||| door asks for (`Native.Support.Obj`, erased): the support tier converts
||| between a value and an object, reads a field, or makes a value, only
||| with the evidence of one, so that no code takes a value for what it is
||| not. A layout statement the code generator does not keep would be a
||| wrong layout, which the tests of the primitive that uses it find.
||| `Immutable` states no layout: it is what a pure load's type asks for
||| (`Types.PureLoad`), and a false one would let a load read a word before
||| or after a write it may not be moved past. The statements are the
||| trusted part, few, and each in one place.
|||
||| The relations are open: a type's statements are made in the module that
||| defines the type, which answers for them, and here only for the types
||| of the libraries Idris ships, which no module of ours defines
||| (`String`, `List`, `Buffer`, the pointers, `Integer`, `Char`). So a
||| package that lays a type of its own over a kind states it with the type,
||| and neither this module nor the code generator changes. The linter
||| checks the place of each statement (`repr-orphan`).
|||
||| Part of the type layer, the modules of `Types`, which the code generator
||| and the runtime's support tier read.
module Native.Types.Repr

import Native.Types.ConId
import Native.Types.Kind

import Data.Buffer

%default total

||| Every value of `a` is an object of kind `k`: a value of `a` can be taken
||| for one. The type decides the kind. A foreign pointer is not one of
||| these, as it is of two kinds (`Repr`).
public export
interface Only (0 k : Kind) (0 a : Type) | a where

||| A string is a `STRING` always, the empty one too.
public export
Only Kind.STRING String where

||| A list is a `CON` always: `[]` a static object of no fields.
public export
Only Kind.CON (List a) where

||| A buffer of `Data.Buffer` is a `BYTES` always, the empty one too.
public export
Only Kind.BYTES Buffer where

||| An object of kind `k` is a value of `a`: one can be given as a value of
||| `a`.
public export
interface Repr (0 k : Kind) (0 a : Type) where

||| A kind that holds every value of a type holds values of it.
public export
Only k a => Repr k a where

||| A foreign pointer is an address outside the heap, as a `PTR`, the null
||| one too;
public export
Repr Kind.PTR (Ptr a) where

public export
Repr Kind.PTR AnyPtr where

||| or, where `base` asks the runtime for a pointer to zero-ended bytes and
||| reads it only through the runtime, the string itself (`Support.Ptr`),
||| as an `AnyPtr` too, which `free` takes.
public export
Repr Kind.STRING (Ptr String) where

public export
Repr Kind.STRING AnyPtr where

||| An `Integer` outside the fixnum range is a `BIGNUM`, under an encoding
||| with fixnums (`Fixnums`).
public export
Repr Kind.BIGNUM Integer where

||| A value of `a` is an object of one of several kinds, whose header says
||| which, or for a type of `Handles` a handle: what a value of such a type
||| is read by (`Support.Obj.asKind`), which takes a handle for no object.
public export
interface Objects (0 a : Type) where

||| A foreign pointer, of either type, is a `PTR` or a `STRING`.
public export
Objects (Ptr a) where

public export
Objects AnyPtr where

||| An `Integer` is a `BIGNUM` where it is no fixnum (`Fixnums`).
public export
Objects Integer where

||| A value of `a` may be a fixnum: a number the system tier gives for a
||| value of its own (`Native.System`), a handle, which the libraries hold
||| only to give back, as `base` holds a file as an `AnyPtr`. A foreign
||| pointer may be one, of either type, as the prelude turns one into the
||| other.
public export
interface Handles (0 a : Type) where

public export
Handles AnyPtr where

public export
Handles (Ptr a) where

||| The ids of `List`'s constructors, `[]` then `(::)`, as it declares them.
export
listNil, listCons : ConId
listNil = ConId.declared 0
listCons = ConId.declared 1

||| Constructor `c` of the data type `t` is a `CON` of the id `c` and `n`
||| fields: a count no code computes with, only the statement's, as the
||| code generator's `ConH` has it. The type and the id decide the count,
||| which a search finds. The ids are qualified in the statements: there a
||| bare `listCons` would be a new variable, and the statement one of
||| every id.
public export
interface ConOf (0 t : Type) (0 c : ConId) (0 n : Nat) | t, c where

public export
ConOf (List a) Repr.listNil 0 where

public export
ConOf (List a) Repr.listCons 2 where

||| Field `i` of constructor `c` of `t` holds a value of `f`.
public export
interface FieldOf (0 t : Type) (0 c : ConId) (0 i : Bits64) (0 f : Type) | t, c, i where

||| The head of a `(::)`;
public export
FieldOf (List a) Repr.listCons 0 a where

||| its tail.
public export
FieldOf (List a) Repr.listCons 1 (List a) where

||| A value of `t` may be a fixnum, the signed integer it stands for: an
||| `Integer` is one exactly where it is in the fixnum range, under an
||| encoding with fixnums, and a `BIGNUM` otherwise, never the other way
||| round, so that one integer has one word.
public export
interface Fixnums (0 t : Type) where

public export
Fixnums Integer where

||| A published value of `a` is never written: once a value of `a` exists,
||| the object it is stays as it is until it is collected. What a pure load
||| asks of the type it reads (`Types.PureLoad`), since such a load may be
||| done at any time, and its result shared.
public export
interface Immutable (0 a : Type) where

||| Ordinary code holds every value of `t` as a fixnum, the integer it
||| stands for: never an object.
public export
interface Immediate (0 t : Type) where

||| A character is its code point.
public export
Immediate Char where
