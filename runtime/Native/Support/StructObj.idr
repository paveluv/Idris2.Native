||| Mutable records (`Types.Struct`) for ordinary code: each operation a flat
||| function with an IO type over the door's (`Native.Support.Obj`), which
||| ordinary code calls as any other.
|||
||| A record is made value by value: `new` of its counts, then `put` of
||| each value field in the order of its values, by its name, then `done`,
||| which gives the record once every value is stored. Its raw words start
||| zero. A field is read by `get` and written by `set`, by its name, as the
||| type its carrier says (`Carried`): a raw word converted to its machine
||| type or its address (`Runtime.Cell`), a value as ordinary code holds it.
||| Which of the two an access is, the field's carrier says where the
||| program is compiled (`Access`): an access is one load or one store.
module Native.Support.StructObj

import Native.Support.Obj

import Native.Carrier
import Native.Field
import Native.Flat.Uniform as Flat
import Native.Mach
import Native.Runtime.ByteAddr
import Native.Runtime.Cell as Runtime
import Native.Runtime.Ordo as Runtime
import Native.Runtime.PortTy
import Native.Types.Struct as Types

%default total

%cg native flat Support.StructObj.new
||| A new record, its names distinct, its raw words zero, none of its
||| values stored yet: the record's type says its fields, and the search on
||| them its counts of raw words and of values, which its header holds.
export covering
new : {raws, values : Bits64} -> {auto 0 counts : Field.Counted fs raws values} ->
      {auto 0 names : Field.distinct fs = True} -> IO (Obj.Building fs 0)
new = primIO $ \w =>
  let (Runtime.MkOrdo # b) = Obj.beginStruct raws values counts Runtime.MkOrdo in MkIORes b w

%cg native flat Support.StructObj.put
||| The record being made with its value of the name stored, the next to
||| store: the search on the name gives its index, which must be the next.
export
put : (0 n : String) -> {j : Bits64} ->
      {auto 0 at : Field.Named n fs i j (Carrier.ValueOf t)} -> {auto 0 next : (j == k) = True} ->
      Obj.Building fs k -> Flat.Uniform t -> IO (Obj.Building fs (k + 1))
put n b x = primIO $ \w =>
  let (Runtime.MkOrdo # b') = Obj.putValue n b x Runtime.MkOrdo in MkIORes b' w

%cg native flat Support.StructObj.done
||| The record, once each of its values is stored.
export
done : {auto 0 counts : Field.Counted fs raws values} -> {auto 0 all : (values == k) = True} ->
       Obj.Building fs k ->
       IO (Flat.Uniform (Types.Struct fs))
done b = primIO $ \w => let (Runtime.MkOrdo # v) = Obj.endStruct b Runtime.MkOrdo in MkIORes v w

%cg native flat Support.StructObj.word
||| The raw word of the name, and storing one: the accesses `get` and `set`
||| are of a raw field, by the index its name gives.
export
word : (0 n : String) -> {i : Bits64} -> {auto 0 at : Field.Named n fs i j c} ->
       {auto 0 raw : Carrier.scanned c = False} -> Flat.Uniform (Types.Struct fs) -> IO Bits64
word n v = primIO $ \w => let (Runtime.MkOrdo # x) =
                                Obj.structWord n v Runtime.MkOrdo in MkIORes x w

%cg native flat Support.StructObj.setWord
export
setWord : (0 n : String) -> {i : Bits64} -> {auto 0 at : Field.Named n fs i j c} ->
          {auto 0 raw : Carrier.scanned c = False} -> Flat.Uniform (Types.Struct fs) ->
          Bits64 -> IO ()
setWord n v x = primIO $ \w =>
  let (Runtime.MkOrdo # ()) = Obj.setStructWord n v x Runtime.MkOrdo in MkIORes () w

%cg native flat Support.StructObj.value
||| The value of the name, and storing one: the accesses of a value field.
export
value : (0 n : String) -> {j : Bits64} ->
        {auto 0 at : Field.Named n fs i j (Carrier.ValueOf t)} ->
        Flat.Uniform (Types.Struct fs) -> IO (Flat.Uniform t)
value n v = primIO $ \w => let (Runtime.MkOrdo # x) =
                                 Obj.structValue n v Runtime.MkOrdo in MkIORes x w

%cg native flat Support.StructObj.setValue
export
setValue : (0 n : String) -> {j : Bits64} ->
           {auto 0 at : Field.Named n fs i j (Carrier.ValueOf t)} ->
           Flat.Uniform (Types.Struct fs) -> Flat.Uniform t -> IO ()
setValue n v x = primIO $ \w =>
  let (Runtime.MkOrdo # ()) = Obj.setStructValue n v x Runtime.MkOrdo in MkIORes () w

||| How a field of the carrier is read and written: a raw word by its index
||| among the raw words, converted (`Cell`), a value by its index among the
||| values. One implementation for each carrier a raw word converts to
||| (`Cell`), with no constraint, and expanded where it is used, so that an
||| access is the one call; a word of `U64` is the word, with no
||| conversion to map over its reading.
public export
interface Access (0 c : Carrier) where
  readField : (0 n : String) -> (i, j : Bits64) -> (0 at : Field.Named n fs i j c) ->
              Flat.Uniform (Types.Struct fs) -> IO (Runtime.PortTy.Carried () c)
  writeField : (0 n : String) -> (i, j : Bits64) -> (0 at : Field.Named n fs i j c) ->
               Flat.Uniform (Types.Struct fs) -> Runtime.PortTy.Carried () c -> IO ()

public export %inline
Access (Carrier.M Mach.U64) where
  readField n i _ at v = word n {i} {at} v
  writeField n i _ at v x = setWord n {i} {at} v x

public export %inline
Access (Carrier.M Mach.IWord) where
  readField n i _ at v = Runtime.Cell.fromCell <$> word n {i} {at} v
  writeField n i _ at v x = setWord n {i} {at} v (Runtime.Cell.toCell x)

public export %inline
Access Carrier.ByteAddr where
  readField n i _ at v = Runtime.Cell.fromCell <$> word n {i} {at} v
  writeField n i _ at v x = setWord n {i} {at} v (Runtime.Cell.toCell x)

public export %inline
Access (Carrier.ValueOf t) where
  readField n _ j at v = value n {j} {at} v
  writeField n _ j at v x = setValue n {j} {at} v x

||| The field of the name, as the type its carrier says, and storing one:
||| expanded where it is used, where its carrier says which access it is.
export %inline
get : (0 n : String) -> {i, j : Bits64} -> {0 c : Carrier} ->
      {auto 0 at : Field.Named n fs i j c} -> Access c => Flat.Uniform (Types.Struct fs) ->
      IO (Runtime.PortTy.Carried () c)
get n v = readField n i j at v

export %inline
set : (0 n : String) -> {i, j : Bits64} -> {0 c : Carrier} ->
      {auto 0 at : Field.Named n fs i j c} -> Access c => Flat.Uniform (Types.Struct fs) ->
      Runtime.PortTy.Carried () c -> IO ()
set n v x = writeField n i j at v x

