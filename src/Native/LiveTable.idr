||| A live table: what an allocation site keeps live across its slow path,
||| as data a slow path shared by every site reads. The site's cold code
||| calls the shared slow path, and its table follows the call; the slow
||| path saves the slots the table lists across `idris_alloc_slow`, the
||| GC-visible ones where the collector forwards them, and reloads them
||| after it.
|||
||| A table is entries of one sub-word width, little-endian: the number of
||| GC-visible slots, the number of raw ones, then the GC-visible slots and
||| the raw ones. The width is the narrowest that holds every entry
||| (`tableWidth`). A slot listed twice is saved twice and reloaded twice,
||| the same word each time, which only takes room: the code generator
||| lists each once.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is): the code generator
||| writes the tables, and the shared slow path reads them where these say.
module Native.LiveTable

import Native.Width

%default total

||| Where a table holds the number of its GC-visible slots, the number of
||| its raw ones, and its first slot, in bytes from its start, by the
||| width of its entries.
public export
gcCountAt, rawCountAt, slotsAt : Width.SubWord -> Nat
gcCountAt _ = 0
rawCountAt w = Width.subWordBytes w
slotsAt w = 2 * Width.subWordBytes w

||| The narrowest width whose entries hold the numbers: none past 32 bits.
public export
tableWidth : List Nat -> Maybe Width.SubWord
tableWidth ns =
  let most = foldl max 0 ns in
  if most < 256 then Just Width.Sub8
    else if most < 65536 then Just Width.Sub16
    else if most < 4294967296 then Just Width.Sub32
    else Nothing

||| The table of the GC-visible slots and the raw ones: its width and its
||| bytes; none if an entry needs more than 32 bits.
public export
table : (gc, raw : List Nat) -> Maybe (Width.SubWord, List Bits8)
table gc raw = do
  let entries = length gc :: length raw :: gc ++ raw
  w <- tableWidth entries
  pure (w, foldr (entry w) [] entries)
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

||| The GC-visible slots and the raw ones of a table of the width, its bytes
||| read as `table` writes them; none if they are not a table's.
public export
tableSlots : Width.SubWord -> List Bits8 -> Maybe (List Nat, List Nat)
tableSlots w bytes = do
  (gc :: raw :: slots) <- entries bytes
    | _ => Nothing
  (gcSlots, rawSlots) <- split gc slots
  if length rawSlots == raw then Just (gcSlots, rawSlots) else Nothing
  where
    -- the first `n` of the entries, and the rest
    split : Nat -> List Nat -> Maybe (List Nat, List Nat)
    split Z ns = Just ([], ns)
    split (S n) [] = Nothing
    split (S n) (x :: ns) = map (\(a, b) => (x :: a, b)) (split n ns)

    -- the entries so far, the one being read, its bytes read and the next
    -- byte's weight: the low byte first
    step : (SnocList Nat, Nat, Nat, Nat) -> Bits8 -> (SnocList Nat, Nat, Nat, Nat)
    step (done, part, have, weight) b =
      let part' = part + weight * cast b in
      if S have == Width.subWordBytes w then (done :< part', 0, 0, 1)
        else (done, part', S have, 256 * weight)

    -- the entries, each the next of the width's bytes
    entries : List Bits8 -> Maybe (List Nat)
    entries bs = case foldl step ([<], 0, 0, 1) bs of
      (done, _, 0, _) => Just (done <>> [])
      _ => Nothing
