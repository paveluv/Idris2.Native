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
||| (`Immediate`); an object is made only with its header written, of parts
||| that fit their fields (`allocate`, `Types.Header.Parts`), so that its
||| kind is its header's, and its header rewritten only so (`setHeader`).
||| Words and bytes are loaded and stored only in objects of the raw shape,
||| which hold no value the collector follows, and only after the header:
||| their offsets are the payload's, from the word after it; in a mutable
||| record (`Types.Struct`), a raw word or a value by its field's name, of
||| a carrier it need not see or of the type of the value
||| (`Field.Named`), a record made value by value in order and given only
||| once each is stored (`beginStruct`, `putValue`, `endStruct`). A handle, a
||| number the system tier gives for a value of its own, is read and made
||| here too (`valueHandle`, `handleValue`). The core's conversions, which
||| take a value of any type, are used outside the core only here, which the
||| linter checks.
module Native.Support.Obj

import Native.Carrier
import Native.Field
import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Space
import Native.Types.ConstructorId as Types
import Native.Types.Header
import Native.Types.Kind as Types
import Native.Types.Represents as Types
import Native.Types.Struct as Types

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The address of an object of the kind `k`: an address of the kind's
||| shape.
export
data Obj : (0 k : Types.Kind) -> Type where
  MkObj : {0 s : HeapObj.Shape} -> (0 shaped : Types.Kind.shape k = Just s) ->
          Runtime.Memory.Addr s -> Obj k

||| The word, or 32, 16 or 8 bits of it, at the offset into the payload of
||| an object of the raw shape.
export %inline
load64, load32, load16, load8 : {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
                                Obj k -> (offset : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
load64 (MkObj _ a) n = Runtime.Memory.load64 a (8 + n)
load32 (MkObj _ a) n = Runtime.Memory.load32 a (8 + n)
load16 (MkObj _ a) n = Runtime.Memory.load16 a (8 + n)
load8 (MkObj _ a) n = Runtime.Memory.load8 a (8 + n)

||| Store the word, or its low 32, 16 or 8 bits, at the offset into the
||| payload of an object of the raw shape.
export %inline
store64, store32, store16, store8 : {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
                                    Obj k -> (offset, value : Bits64) ->
                                    Runtime.Ordo.Op Runtime.Ordo ()
store64 (MkObj _ a) n = Runtime.Memory.store64 a (8 + n)
store32 (MkObj _ a) n = Runtime.Memory.store32 a (8 + n)
store16 (MkObj _ a) n = Runtime.Memory.store16 a (8 + n)
store8 (MkObj _ a) n = Runtime.Memory.store8 a (8 + n)

||| An object's header word.
export %inline
header : Obj k -> Runtime.Ordo.Op Runtime.Ordo Bits64
header (MkObj _ a) = Runtime.Memory.load64 a 0

||| The header of parts that all fit, or the end of the program.
export
checked : (k : Types.Kind) -> Types.Header.Parts k -> Runtime.Ordo.Op Runtime.Ordo Bits64
checked k ps =
  if Types.Header.allFit ps then Runtime.Ordo.pure (Types.Header.headerWord k ps)
  else Runtime.Ordo.crashOp "idris: a header part too large for its field"

||| A new object of the kind `k`, of the raw shape, its header the kind's
||| with the parts, as many words as the header says, its last word zero,
||| so that a string's padding is; the payload still to be written. The
||| program ends for a part too large for its field.
export %inline
allocate : (k : Types.Kind) -> {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
           Types.Header.Parts k -> Runtime.Ordo.Op Runtime.Ordo (Obj k)
allocate k ps = do
  h <- checked k ps
  let words = HeapObj.Shape.headerObjectWords h
  a <- Runtime.Space.allocate (8 * words)
  let o = Runtime.Memory.objectAt a
  Runtime.Memory.store64 o 0 h
  if words == 1 then Runtime.Ordo.pure (MkObj raw o) else do
    Runtime.Memory.store64 o (8 * (words - 1)) 0
    Runtime.Ordo.pure (MkObj raw o)

||| An object's header rewritten, its kind's with the parts, of the same
||| size, as a string's is once its bytes are known to be ASCII or not.
||| The program ends for a part too large for its field.
export %inline
setHeader : {k : Types.Kind} -> {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
            Obj k -> Types.Header.Parts k -> Runtime.Ordo.Op Runtime.Ordo ()
setHeader (MkObj _ a) ps = do
  h <- checked k ps
  Runtime.Memory.store64 a 0 h

||| The bytes of an object's payload from the offset, by its byte address: for
||| the system to read or write them.
export %inline
objectBytes : Obj k -> (offset : Bits64) -> Runtime.ByteAddr
objectBytes (MkObj _ a) n = Runtime.Memory.objectBytes a (8 + n)

||| The object a value is, of a kind that holds every value of its type.
export %inline
valueObject : {auto 0 only : Types.Represents.Only k a} ->
              {auto 0 shaped : Types.Kind.shape k = Just s} ->
              Flat.Uniform a -> Runtime.Ordo.Op Runtime.Ordo (Obj k)
valueObject v = do
  a <- Runtime.Memory.valueObject v
  Runtime.Ordo.pure (MkObj shaped a)

||| The value an object is, of a type its kind holds values of.
export %inline
objectValue : {auto 0 rep : Types.Represents k a} -> Obj k ->
              Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform a)
objectValue (MkObj _ a) = Runtime.Memory.objectValue a

||| The object a value is, if it is one of the kind `k`, for a type whose
||| values are objects of several kinds, each told by its header: by the
||| header's kind code (`Types.Kind.headerCode`), compared with `k`'s.
export %inline
asKind : (k : Types.Kind) -> {auto 0 objs : Types.Represents.Objects a} ->
         {auto 0 rep : Types.Represents k a} ->
         {auto 0 shaped : Types.Kind.shape k = Just s} -> Flat.Uniform a ->
         Runtime.Ordo.Op Runtime.Ordo (Maybe (Obj k))
asKind k v = do
  w <- Runtime.Memory.valueWord v
  pointer <- Runtime.Memory.isPointer w
  if not pointer then Runtime.Ordo.pure Nothing else do
    -- every value of the type but a handle is an object, whose header is
    -- at 0, whatever its shape
    a <- Runtime.Memory.valueObject {s} v
    h <- Runtime.Memory.load64 a 0
    if Types.Kind.headerCode h == Types.Kind.code k
      then Runtime.Ordo.pure (Just (MkObj shaped a))
      else Runtime.Ordo.pure Nothing

||| The number a handle is, if a value of a type of `Handles` is one, and
||| the value of a handle.
export %inline
valueHandle : {auto 0 hs : Types.Represents.Handles a} -> Flat.Uniform a ->
              Runtime.Ordo.Op Runtime.Ordo (Maybe Bits64)
valueHandle v = do
  w <- Runtime.Memory.valueWord v
  pointer <- Runtime.Memory.isPointer w
  Runtime.Ordo.pure (if pointer then Nothing else Just (Runtime.Memory.wordFixnum w))

export %inline
handleValue : {auto 0 hs : Types.Represents.Handles a} -> (number : Bits64) ->
              Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform a)
handleValue n = do
  w <- Runtime.Memory.fixnumWord n
  Runtime.Memory.fieldValue w

||| The integer a fixnum stands for, of a type held as fixnums, and the
||| value of one.
export %inline
immediate : {auto 0 imm : Types.Represents.Immediate t} -> Flat.Uniform t ->
            Runtime.Ordo.Op Runtime.Ordo Bits64
immediate v = do
  w <- Runtime.Memory.valueWord v
  Runtime.Ordo.pure (Runtime.Memory.wordFixnum w)

export %inline
ofImmediate : {auto 0 imm : Types.Represents.Immediate t} -> Bits64 ->
              Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
ofImmediate n = do
  w <- Runtime.Memory.fixnumWord n
  Runtime.Memory.fieldValue w

||| A value of the data type `t` that is its constructor `c`.
export
data Con : (0 t : Type) -> (0 c : Types.ConstructorId) -> Type where
  MkCon : Runtime.Memory.Addr HeapObj.Shape.VALUES -> Con t c

||| The value as its constructor `c`, if it is that one: by its header's
||| constructor id.
export %inline
asCon : (c : Types.ConstructorId) -> {auto 0 only : Types.Represents.Only Types.Kind.CON t} ->
        {auto 0 con : Types.Represents.IsCon t c} ->
        Flat.Uniform t -> Runtime.Ordo.Op Runtime.Ordo (Maybe (Con t c))
asCon c v = do
  a <- Runtime.Memory.valueObject {s = HeapObj.Shape.VALUES} v
  h <- Runtime.Memory.load64 a 0
  if Types.ConstructorId.fromHeader h == c then Runtime.Ordo.pure (Just (MkCon a))
    else Runtime.Ordo.pure Nothing

||| Field `i` of a constructor, as the value it holds.
export %inline
field : (i : Bits64) -> {auto 0 fld : Types.Represents.FieldOf t c i f} -> Con t c ->
        Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform f)
field i (MkCon a) = do
  w <- Runtime.Memory.load64 a (8 + 8 * i)
  Runtime.Memory.fieldValue w

||| A new value of constructor `c` of no fields, and of two, each field a
||| value of the type the contract gives it.
export %inline
con0 : (c : Types.ConstructorId) -> {auto 0 only : Types.Represents.Only Types.Kind.CON t} ->
       {auto 0 con : Types.Represents.ConOf t c 0} ->
       Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
con0 c = do
  h <- checked Types.Kind.CON (Types.ConstructorId.withConstructor c Types.Header.noParts)
  a <- Runtime.Space.allocate 8
  let o = Runtime.Memory.objectAt {s = HeapObj.Shape.VALUES} a
  Runtime.Memory.store64 o 0 h
  Runtime.Memory.objectValue o

export %inline
con2 : (c : Types.ConstructorId) -> {auto 0 only : Types.Represents.Only Types.Kind.CON t} ->
       {auto 0 con : Types.Represents.ConOf t c 2} ->
       {auto 0 f0 : Types.Represents.FieldOf t c 0 a0} ->
       {auto 0 f1 : Types.Represents.FieldOf t c 1 a1} ->
       Flat.Uniform a0 -> Flat.Uniform a1 -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
con2 c x y = do
  h <- checked Types.Kind.CON
         (Types.ConstructorId.withConstructor c
           (Types.Header.withPart Types.Header.ConArity 2 Types.Header.noParts))
  wx <- Runtime.Memory.valueWord x
  wy <- Runtime.Memory.valueWord y
  a <- Runtime.Space.allocate 24
  let o = Runtime.Memory.objectAt {s = HeapObj.Shape.VALUES} a
  Runtime.Memory.store64 o 0 h
  Runtime.Memory.store64 o 8 wx
  Runtime.Memory.store64 o 16 wy
  Runtime.Memory.objectValue o

||| A mutable record being made, its first `k` values stored: as it is held,
||| the record itself.
export
record Building (0 fs : List (String, Carrier)) (0 k : Bits64) where
  constructor MkBuilding
  made : Flat.Uniform (Types.Struct fs)

||| A new mutable record of the counts of raw words and of values its fields
||| have, its raw words zero, none of its values stored yet: each word 0,
||| which the collector takes for no pointer.
export %inline covering
beginStruct : (raws, values : Bits64) -> (0 counts : Field.Counted fs raws values) ->
              Runtime.Ordo.Op Runtime.Ordo (Building fs 0)
beginStruct raws values _ = do
  h <- checked Types.Kind.STRUCT
         (Types.Header.withPart Types.Header.StructRaws raws
           (Types.Header.withPart Types.Header.StructValues values Types.Header.noParts))
  let words = HeapObj.Shape.headerObjectWords h
  a <- Runtime.Space.allocate (8 * words)
  let o = Runtime.Memory.objectAt {s = HeapObj.Shape.MIXED} a
  Runtime.Memory.store64 o 0 h
  Runtime.Memory.fillBytes (Runtime.Memory.objectBytes o 8) (8 * (words - 1)) 0
  v <- Runtime.Memory.objectValue o
  Runtime.Ordo.pure (MkBuilding v)

||| The byte offset of value `j` of a mutable record: after its header and
||| its raw words, which the header counts.
valueOffset : Runtime.Memory.Addr HeapObj.Shape.MIXED -> (j : Bits64) ->
              Runtime.Ordo.Op Runtime.Ordo Bits64
valueOffset o j = do
  h <- Runtime.Memory.load64 o 0
  Runtime.Ordo.pure (8 + 8 * (HeapObj.Shape.field HeapObj.Shape.Raws h + j))

||| The record being made with its value of the name stored, the next to
||| store.
export %inline
putValue : (0 n : String) -> {j : Bits64} ->
           {auto 0 at : Field.Named n fs i j (Carrier.ValueOf t)} ->
           {auto 0 next : (j == k) = True} ->
           Building fs k -> Flat.Uniform t -> Runtime.Ordo.Op Runtime.Ordo (Building fs (k + 1))
putValue _ (MkBuilding v) x = do
  o <- Runtime.Memory.valueObject {s = HeapObj.Shape.MIXED} v
  off <- valueOffset o j
  w <- Runtime.Memory.valueWord x
  Runtime.Memory.store64 o off w
  Runtime.Ordo.pure (MkBuilding v)

||| The mutable record made, once each of its values is stored.
export %inline
endStruct : {auto 0 counts : Field.Counted fs raws values} -> {auto 0 all : (values == k) = True} ->
            Building fs k ->
            Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform (Types.Struct fs))
endStruct (MkBuilding v) = Runtime.Ordo.pure v

||| The raw word of the name of a mutable record, and storing one: a word
||| the collector never reads, of a carrier it need not see.
export %inline
structWord : (0 n : String) -> {i : Bits64} -> {auto 0 at : Field.Named n fs i j c} ->
             {auto 0 raw : Carrier.scanned c = False} -> Flat.Uniform (Types.Struct fs) ->
             Runtime.Ordo.Op Runtime.Ordo Bits64
structWord _ v = do
  o <- Runtime.Memory.valueObject {s = HeapObj.Shape.MIXED} v
  Runtime.Memory.load64 o (8 + 8 * i)

export %inline
setStructWord : (0 n : String) -> {i : Bits64} -> {auto 0 at : Field.Named n fs i j c} ->
                {auto 0 raw : Carrier.scanned c = False} -> Flat.Uniform (Types.Struct fs) ->
                (value : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
setStructWord _ v x = do
  o <- Runtime.Memory.valueObject {s = HeapObj.Shape.MIXED} v
  Runtime.Memory.store64 o (8 + 8 * i) x

||| The value of the name of a mutable record, and storing one.
export %inline
structValue : (0 n : String) -> {j : Bits64} ->
              {auto 0 at : Field.Named n fs i j (Carrier.ValueOf t)} ->
              Flat.Uniform (Types.Struct fs) -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform t)
structValue _ v = do
  o <- Runtime.Memory.valueObject {s = HeapObj.Shape.MIXED} v
  off <- valueOffset o j
  w <- Runtime.Memory.load64 o off
  Runtime.Memory.fieldValue w

export %inline
setStructValue : (0 n : String) -> {j : Bits64} ->
                 {auto 0 at : Field.Named n fs i j (Carrier.ValueOf t)} ->
                 Flat.Uniform (Types.Struct fs) -> Flat.Uniform t -> Runtime.Ordo.Op Runtime.Ordo ()
setStructValue _ v x = do
  o <- Runtime.Memory.valueObject {s = HeapObj.Shape.MIXED} v
  off <- valueOffset o j
  w <- Runtime.Memory.valueWord x
  Runtime.Memory.store64 o off w
