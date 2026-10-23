||| The named fields of a run of words (`Named`), as a mutable record of the
||| heap (`Types.Struct`) and the runtime's state lay theirs out: each field
||| a name and a carrier (`Native.Carrier`), written `"start" ~: Mach.IWord`
||| for a raw word, which the collector never reads, and `"input" ~& Buffer`
||| for a value, which it scans and may move.
|||
||| The raw words come first, then the values, whatever order the fields are
||| written in; a field is found by its name, where the program is compiled,
||| by a search on the list (`Named`), which gives its index among the
||| fields of its kind and its carrier. So an access names a field the list
||| has, and reads or writes it as the type its carrier says, with no index
||| written and none that could be wrong. A raw field's carrier is one the
||| collector need not see (`~:` refuses a value's), and `Value`, any value
||| of a call, has no place in a field.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Field

import Native.Carrier
import Native.Mach

%default total

export infix 2 ~:, ~&

||| What may be written right of a raw field's name: a machine type, whose
||| carrier it holds, or a carrier.
public export
interface Raw a where
  carrier : a -> Carrier

public export
Raw Mach where
  carrier m = Carrier.M m

public export
Raw Carrier where
  carrier c = c

||| A raw field: a word of the carrier, which the collector need not see.
public export
(~:) : Raw a => String -> (x : a) -> {auto 0 raw : Carrier.scanned (carrier x) = False} ->
       (String, Carrier)
n ~: x = (n, carrier x)

||| A value field: a value of the type, as ordinary code holds it.
public export
(~&) : String -> Type -> (String, Carrier)
n ~& t = (n, Carrier.ValueOf t)

||| The field of the name in the list: its index among the raw fields and
||| among the values before it, the one of its kind its index, and its
||| carrier. Found by the search on the name and the list alone: a name
||| the list does not have finds none. The indices are sums of the
||| primitive addition, which a flat form's static arguments fold, not of
||| `Num`'s, whose method they could not.
public export
data Named : (name : String) -> (fs : List (String, Carrier)) -> (raw, value : Bits64) ->
             (c : Carrier) -> Type where
  [search name fs]
  Here : Named n ((n, c) :: fs) 0 0 c
  ThereRaw : {auto 0 raw : Carrier.scanned c' = False} -> Named n fs i j c ->
             Named n ((m, c') :: fs) (prim__add_Bits64 i 1) j c
  ThereValue : Named n fs i j c -> Named n ((m, Carrier.ValueOf t) :: fs) i (prim__add_Bits64 j 1) c

||| The numbers of the list's raw fields and of its values. Found by the
||| search on the list alone, so that where they are left to it, the
||| numbers are its indices, sums of literals that fold to literals, as
||| `Named`'s are, never a count of the list made where the program runs.
public export
data Counted : (fs : List (String, Carrier)) -> (raws, values : Bits64) -> Type where
  [search fs]
  NoFields : Counted [] 0 0
  RawField : {auto 0 raw : Carrier.scanned c = False} -> Counted fs i j ->
             Counted ((n, c) :: fs) (prim__add_Bits64 i 1) j
  ValueField : Counted fs i j -> Counted ((n, Carrier.ValueOf t) :: fs) i (prim__add_Bits64 j 1)

||| The list's numbers of raw fields and of values, as the search finds
||| them: where a number is known beforehand, it is compared with these,
||| since the search cannot work back from a sum to its terms.
public export
counts : (0 fs : List (String, Carrier)) -> {raws, values : Bits64} ->
         {auto 0 counted : Counted fs raws values} -> (Bits64, Bits64)
counts _ = (raws, values)

||| Whether the fields' names are each one field's.
public export
distinct : List (String, Carrier) -> Bool
distinct [] = True
distinct ((n, _) :: fs) = all ((/= n) . fst) fs && distinct fs
