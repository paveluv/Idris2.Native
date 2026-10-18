||| A constructor's id (`ConstructorId`): which constructor of its data type
||| an object is, from 0 in the order of the type's declaration, in its
||| header's `ConId` part.
|||
||| An identity, not a number: two are compared, and nothing else. No
||| arithmetic applies (there is no `Num`), so an id is not computed, nor a
||| count or another code taken for one. One is a constructor's place in its
||| type's declaration (`declared`), which the representation contract names
||| (`Types.Represents.listCons`), or read from a header (`ofHeader`); one
||| goes only into a header (`withConstructor`). No literal is one: a
||| `fromInteger` of its own would leave every literal of a module that
||| imports it two readings.
|||
||| Part of the type layer, the modules of `Types`, which the code generator
||| and the runtime's support tier read.
module Native.Types.ConstructorId

import Native.Types.Header
import Native.Types.Kind

%default total

||| A constructor's id.
export
record ConstructorId where
  constructor MkConstructorId
  word : Bits64

export
Eq ConstructorId where
  a == b = a.word == b.word

||| The id of the constructor `n` after the first in its type's
||| declaration.
export %inline
declared : (n : Bits64) -> ConstructorId
declared n = MkConstructorId n

||| The id a constructor's header holds.
export %inline
ofHeader : (header : Bits64) -> ConstructorId
ofHeader h = MkConstructorId (Header.readPart Header.ConId h)

||| A constructor's header parts with its id.
export %inline
withConstructor : ConstructorId -> Header.Parts Kind.CON -> Header.Parts Kind.CON
withConstructor c = Header.withPart Header.ConId c.word
