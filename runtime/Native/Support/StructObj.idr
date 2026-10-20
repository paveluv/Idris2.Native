||| Mutable records (`Types.Struct`) for ordinary code: each operation a flat
||| function with an IO type over the door's (`Native.Support.Obj`), which
||| ordinary code calls as any other.
|||
||| A record is made value by value: `new` of its counts, then `put` of
||| each value in order, each of the type the record has there, then
||| `done`, which gives the record once every value is stored. Its raw
||| words start zero; they are read and written by `readWord` and
||| `writeWord`, its values by `readValue` and `writeValue`, each by an
||| index its type allows.
module Native.Support.StructObj

import Native.Support.Obj

import Native.Flat.Uniform as Flat
import Native.Runtime.Ordo as Runtime
import Native.Types.Struct as Types

%default total

%cg native flat Support.StructObj.new
||| A new record of the counts of raw words and of values its type has,
||| which the witnesses tie to it, its raw words zero, none of its values
||| stored yet: `new 2 1` of a `Struct 2 [a]`.
export covering
new : (raws, values : Bits64) -> {auto 0 rs : Types.Struct.Sized raws r} ->
      {auto 0 sv : Types.Struct.Sized values (length vs)} -> IO (Obj.Building r vs 0)
new raws values = primIO $ \w =>
  let (Runtime.MkOrdo # b) = Obj.beginStruct raws values rs sv Runtime.MkOrdo in MkIORes b w

%cg native flat Support.StructObj.put
||| The record being made with its value `i` stored, the next to store.
export
put : (i : Bits64) -> {auto 0 next : cast i = k} ->
      {auto 0 inside : Types.Struct.Below k (length vs)} ->
      Obj.Building r vs k -> Flat.Uniform (Types.Struct.valueType vs inside) ->
        IO (Obj.Building r vs (S k))
put i b x = primIO $ \w =>
  let (Runtime.MkOrdo # b') = Obj.putValue i b x Runtime.MkOrdo in MkIORes b' w

%cg native flat Support.StructObj.done
||| The record, once each of its values is stored.
export
done : {auto 0 all : k = length vs} -> Obj.Building r vs k -> IO (Flat.Uniform (Types.Struct r vs))
done b = primIO $ \w => let (Runtime.MkOrdo # v) = Obj.endStruct b Runtime.MkOrdo in MkIORes v w

%cg native flat Support.StructObj.readWord
||| Raw word `i` of the record, and storing one.
export
readWord : (i : Bits64) -> {auto 0 inside : Types.Struct.Below (cast i) r} ->
       Flat.Uniform (Types.Struct r vs) -> IO Bits64
readWord i v = primIO $ \w => let (Runtime.MkOrdo # x) =
                                    Obj.structWord i v Runtime.MkOrdo in MkIORes x w

%cg native flat Support.StructObj.writeWord
export
writeWord : (i : Bits64) -> {auto 0 inside : Types.Struct.Below (cast i) r} ->
          Flat.Uniform (Types.Struct r vs) -> (value : Bits64) -> IO ()
writeWord i v x = primIO $ \w =>
  let (Runtime.MkOrdo # ()) = Obj.setStructWord i v x Runtime.MkOrdo in MkIORes () w

%cg native flat Support.StructObj.readValue
||| Value `i` of the record, and storing one.
export
readValue : (i : Bits64) -> {auto 0 inside : Types.Struct.Below (cast i) (length vs)} ->
            Flat.Uniform (Types.Struct r vs) -> IO (Flat.Uniform (Types.Struct.valueType vs inside))
readValue i v = primIO $ \w => let (Runtime.MkOrdo # x) =
                                     Obj.structValue i v Runtime.MkOrdo in MkIORes x w

%cg native flat Support.StructObj.writeValue
export
writeValue : (i : Bits64) -> {auto 0 inside : Types.Struct.Below (cast i) (length vs)} ->
             Flat.Uniform (Types.Struct r vs) -> Flat.Uniform (Types.Struct.valueType vs inside) ->
               IO ()
writeValue i v x = primIO $ \w =>
  let (Runtime.MkOrdo # ()) = Obj.setStructValue i v x Runtime.MkOrdo in MkIORes () w
