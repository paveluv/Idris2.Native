||| Objects by their kind (`Obj`): the support tier's addresses, and its one
||| door between values and objects. The core knows an object by its shape
||| only (`Memory.Addr`); the support tier, which implements the built-in
||| types, knows the kind too, so that a string's address is not taken for
||| a list cell's. An `Obj k` is an address of the kind's shape, with the
||| kind; only this module makes one.
|||
||| Nothing here takes a value for what it is not: each conversion asks the
||| evidence of the representation contract (`Types.Represents`). A value
||| becomes an object of a kind that holds every value of its type
||| (`Only`), an object a value of a type the kind holds (`Represents`); a
||| constructor of a data type is read through a view of its fields
||| (`asCon`, `field`, by `ConOf` and `FieldOf`) and made whole (`con0`,
||| `con2`); a fixnum is read and made as the integer it stands for
||| (`Immediate`); an object is made only with its header written
||| (`allocate`), so that its kind is its header's. Words and bytes are
||| loaded and stored only in objects of the raw shape, which hold no value
||| the collector follows. The core's conversions, which take a value of
||| any type, are used outside the core only here, which the linter checks.
module Native.Support.Obj

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches the inline wrappers'
-- bodies, which use the core's accesses, so it is loaded wherever this
-- module is)
import public Native.Runtime.Memory

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Runtime.Space
import Native.Types.Header as Types
import Native.Types.Kind as Types
import Native.Types.Represents as Types

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The address of an object of the kind `k`: an address of the kind's
||| shape.
export
data Obj : (0 k : Types.Kind) -> Type where
  MkObj : {0 s : HeapObj.Shape} -> (0 shaped : Types.Kind.shapeOf k = Just s) -> Runtime.Memory.Addr s -> Obj k

||| The word, or 32, 16 or 8 bits of it, at the object plus the offset, in
||| an object of the raw shape.
export %inline
load64, load32, load16, load8 : {auto 0 raw : Types.Kind.shapeOf k = Just HeapObj.Shape.RAW} ->
                                Obj k -> (offset : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
load64 (MkObj _ a) = Runtime.Memory.load64 a
load32 (MkObj _ a) = Runtime.Memory.load32 a
load16 (MkObj _ a) = Runtime.Memory.load16 a
load8 (MkObj _ a) = Runtime.Memory.load8 a

||| Store the word, or its low 32, 16 or 8 bits, at the object plus the
||| offset, in an object of the raw shape.
export %inline
store64, store32, store16, store8 : {auto 0 raw : Types.Kind.shapeOf k = Just HeapObj.Shape.RAW} ->
                                    Obj k -> (offset, value : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
store64 (MkObj _ a) = Runtime.Memory.store64 a
store32 (MkObj _ a) = Runtime.Memory.store32 a
store16 (MkObj _ a) = Runtime.Memory.store16 a
store8 (MkObj _ a) = Runtime.Memory.store8 a

||| A new object of the kind `k`, of the raw shape, its header `fixedWord`
||| and the parts given (`Types.Header.partBits`), as many words as the
||| header says, its last word zero, so that a string's padding is; the
||| rest still to be written.
export %inline
allocate : (k : Types.Kind) -> {auto 0 raw : Types.Kind.shapeOf k = Just HeapObj.Shape.RAW} ->
           (parts : Bits64) -> Runtime.Ordo.Op Runtime.Ordo (Obj k)
allocate k parts = do
  let header = Types.Header.fixedWord k + parts
      words = HeapObj.Shape.objectWordsOf header
  a <- Runtime.Space.allocate (8 * words)
  let o = MkObj raw (Runtime.Memory.objectAt a)
  store64 o 0 header
  if words == 1 then Runtime.Ordo.pure o else do
    store64 o (8 * (words - 1)) 0
    Runtime.Ordo.pure o

||| An object's bytes from the offset, as raw memory: for the system to
||| read or write them.
export %inline
objectBytes : Obj k -> (offset : Bits64) -> Runtime.Raw
objectBytes (MkObj _ a) n = Runtime.Memory.objectBytes a n

||| The object a value is, of a kind that holds every value of its type.
export %inline
valueObject : {auto 0 only : Types.Represents.Only k a} -> {auto 0 shaped : Types.Kind.shapeOf k = Just s} ->
              Flat.Uniform a -> Runtime.Ordo.Op Runtime.Ordo (Obj k)
valueObject v = do
  a <- Runtime.Memory.valueObject v
  Runtime.Ordo.pure (MkObj shaped a)

||| The value an object is, of a type its kind holds values of.
export %inline
objectValue : {auto 0 rep : Types.Represents k a} -> Obj k -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform a)
objectValue (MkObj _ a) = Runtime.Memory.objectValue a

||| The integer a fixnum stands for, of a type held as fixnums, and the
||| value of one.
export %inline
immediate : {auto 0 imm : Types.Represents.Immediate t} -> Flat.Uniform t -> Runtime.Ordo.Op Runtime.Ordo Bits64
immediate v = do
  w <- Runtime.Memory.valueWord v
  Runtime.Ordo.pure (Runtime.Memory.fixnumOf w)

export %inline
ofImmediate : {auto 0 imm : Types.Represents.Immediate t} -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
ofImmediate n = do
  w <- Runtime.Memory.fixnumWord n
  Runtime.Memory.fieldValue w

||| A value of the data type `t` that is its constructor `c`.
export
data Con : (0 t : Type) -> (0 c : Bits64) -> Type where
  MkCon : Runtime.Memory.Addr HeapObj.Shape.VALUES -> Con t c

||| The value as its constructor `c`, if it is that one: by its header's
||| constructor id.
export %inline
asCon : (c : Bits64) -> {auto 0 only : Types.Represents.Only Types.Kind.CON t} -> {auto 0 con : Types.Represents.IsCon t c} ->
        Flat.Uniform t -> Runtime.Ordo.Op Runtime.Ordo (Maybe (Con t c))
asCon c v = do
  a <- Runtime.Memory.valueObject {s = HeapObj.Shape.VALUES} v
  h <- Runtime.Memory.load64 a 0
  if Types.Header.readPart Types.Header.ConId h == c then Runtime.Ordo.pure (Just (MkCon a)) else Runtime.Ordo.pure Nothing

||| Field `i` of a constructor, as the value it holds.
export %inline
field : (i : Bits64) -> {auto 0 fld : Types.Represents.FieldOf t c i f} -> Con t c -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform f)
field i (MkCon a) = do
  w <- Runtime.Memory.load64 a (8 + 8 * i)
  Runtime.Memory.fieldValue w

||| A new value of constructor `c` of no fields, and of two, each field a
||| value of the type the contract gives it.
export %inline
con0 : (c : Bits64) -> {auto 0 only : Types.Represents.Only Types.Kind.CON t} -> {auto 0 con : Types.Represents.ConOf t c 0} ->
       Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
con0 c = do
  a <- Runtime.Space.allocate 8
  let o = Runtime.Memory.objectAt {s = HeapObj.Shape.VALUES} a
  Runtime.Memory.store64 o 0 (Types.Header.fixedWord Types.Kind.CON + Types.Header.partBits Types.Header.ConId c)
  Runtime.Memory.objectValue o

export %inline
con2 : (c : Bits64) -> {auto 0 only : Types.Represents.Only Types.Kind.CON t} -> {auto 0 con : Types.Represents.ConOf t c 2} ->
       {auto 0 f0 : Types.Represents.FieldOf t c 0 a0} -> {auto 0 f1 : Types.Represents.FieldOf t c 1 a1} ->
       Flat.Uniform a0 -> Flat.Uniform a1 -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
con2 c x y = do
  wx <- Runtime.Memory.valueWord x
  wy <- Runtime.Memory.valueWord y
  a <- Runtime.Space.allocate 24
  let o = Runtime.Memory.objectAt {s = HeapObj.Shape.VALUES} a
  Runtime.Memory.store64 o 0
    (Types.Header.fixedWord Types.Kind.CON + Types.Header.partBits Types.Header.ConId c + Types.Header.partBits Types.Header.ConArity 2)
  Runtime.Memory.store64 o 8 wx
  Runtime.Memory.store64 o 16 wy
  Runtime.Memory.objectValue o
