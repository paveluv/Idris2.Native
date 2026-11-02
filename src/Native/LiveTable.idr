||| A live table: what an allocation site keeps live across its slow path
||| that the collector must see, as data a slow path shared by every site
||| reads. The site's cold code calls the shared slow path, and its table
||| follows the call; the slow path puts the words the table lists in
||| `ROOTS` across `idris_alloc_slow`, where the collector forwards them,
||| and reloads them after it. Only GC-visible words are listed. A raw slot
||| needs nothing: nothing the slow path runs writes `SCRATCH`, since the
||| runtime is Direct code, which keeps its slots in frames of its own, and
||| the collector never reads it.
|||
||| An entry is a word by its index among the words of the registers' save
||| area and `SCRATCH` after it, as the target's slow path lays them out: a
||| register, which that slow path saves there, by its own, a slot past
||| them. A table is entries of one sub-word width, little-endian: twice the
||| number of entries, plus one if the slow path is to save the
||| floating-point registers too, then the entries. The width is the
||| narrowest that holds every number (`tableWidth`). A word listed twice
||| is saved twice and reloaded twice, the same word each time, which only
||| takes room: the code generator lists each once.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is): the code generator
||| writes the tables, and the shared slow path reads them where these say.
module Native.LiveTable

import Native.Width

%default total

||| Where a table holds its count, and its first entry, in bytes from its
||| start, by the width of its entries.
public export
countAt, entriesAt : Width.SubWord -> Nat
countAt _ = 0
entriesAt w = Width.subWordBytes w

||| The narrowest width whose entries hold the numbers: none past 32 bits.
public export
tableWidth : List Nat -> Maybe Width.SubWord
tableWidth ns =
  let most = foldl max 0 ns in
  if most < 256 then Just Width.Sub8
    else if most < 65536 then Just Width.Sub16
    else if most < 4294967296 then Just Width.Sub32
    else Nothing

||| The table of the GC-visible words' entries, and whether the
||| floating-point registers are to be saved: its width and its bytes; none
||| if a number needs more than 32 bits.
public export
table : (floats : Bool) -> (entries : List Nat) -> Maybe (Width.SubWord, List Bits8)
table floats entries = do
  let numbers = (2 * length entries + (if floats then 1 else 0)) :: entries
  w <- tableWidth numbers
  pure (w, foldr (entry w) [] numbers)
  where
    -- the entry's bytes, the low first, before the rest
    entry : Width.SubWord -> Nat -> List Bits8 -> List Bits8
    entry Width.Sub8 n rest = cast n :: rest
    entry Width.Sub16 n rest =
      let v = the Bits64 (cast n) in cast v :: cast (prim__shr_Bits64 v 8) :: rest
    entry Width.Sub32 n rest =
      let v = the Bits64 (cast n) in
      cast v :: cast (prim__shr_Bits64 v 8) :: cast (prim__shr_Bits64 v 16)
        :: cast (prim__shr_Bits64 v 24) :: rest

||| Whether a table of the width says to save the floating-point registers,
||| and its entries, its bytes read as `table` writes them; none if they are
||| not a table's.
public export
tableEntries : Width.SubWord -> List Bits8 -> Maybe (Bool, List Nat)
tableEntries w bytes = do
  (count :: entries) <- numbers bytes
    | _ => Nothing
  if 2 * length entries + (if odd count then 1 else 0) == count
    then Just (odd count, entries) else Nothing
  where
    -- the entries so far, the one being read, its bytes read and the next
    -- byte's weight: the low byte first
    step : (SnocList Nat, Nat, Nat, Nat) -> Bits8 -> (SnocList Nat, Nat, Nat, Nat)
    step (done, part, have, weight) b =
      let part' = part + weight * cast b in
      if S have == Width.subWordBytes w then (done :< part', 0, 0, 1)
        else (done, part', S have, 256 * weight)

    odd : Nat -> Bool
    odd n = prim__and_Bits64 (cast n) 1 == 1

    -- the numbers, each the next of the width's bytes
    numbers : List Bits8 -> Maybe (List Nat)
    numbers bs = case foldl step ([<], 0, 0, 1) bs of
      (done, _, 0, _) => Just (done <>> [])
      _ => Nothing
