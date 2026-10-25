-- The runtime takes no value for what it is not: each conversion between a
-- value, as ordinary code holds it (`Uniform a`), and an object of the
-- heap asks the evidence of the representation contract
-- (`Native.Types.Repr`), which states, once, how the code generator
-- lays values out. This file typechecks exactly when each `failing` block
-- fails, for the reason it names, and the rest checks.
--
-- The contract's statements, in surface Idris terms:
--
--     Only STRING String               -- every String is a STRING object
--     Only CON (List a)                -- every list is a CON: [] or (::)
--     ConOf (List a) listCons 2        -- (::), declared second, has 2 fields
--     FieldOf (List a) listCons 0 a    -- its field 0, the head, is an a
--     FieldOf (List a) listCons 1 (List a)  -- its field 1, the tail, a list
--     Immediate Char                   -- a Char is held as its code point
--     Repr PTR (Ptr a)                 -- a pointer may be an address,
--     Repr STRING (Ptr String)         -- or, to zero-ended bytes, a string
--     Objects (Ptr a)                  -- either way an object, its header
--                                      -- saying which
--
-- So `fastPack`'s walk down a list of characters reads, with each step
-- checked:
--
--     cell <- asCon listCons xs        -- Just the (::), or Nothing at []
--     h <- field 0 cell                -- a Uniform Char
--     c <- immediate h                 -- its code point
--     t <- field 1 cell                -- a Uniform (List Char)
module Contract

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape
import Native.Runtime.Ordo
import Native.Support.Obj
import Native.Types.ConId
import Native.Types.Kind
import Native.Types.Repr

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default covering

-- a string as its object and back
roundTrip : Flat.Uniform String -> Op Ordo (Flat.Uniform String)
roundTrip s = do
  o <- Obj.valueObject {k = STRING} s
  Obj.objectValue o

-- the code point of a list's first character, 0 for []
firstChar : Flat.Uniform (List Char) -> Op Ordo Bits64
firstChar xs = do
  cell <- asCon {t = List Char} listCons xs
  case cell of
    Nothing => pure 0
    Just c => do
      h <- field {f = Char} 0 c
      immediate h

-- a character put in front of a list
cons : Flat.Uniform Char -> Flat.Uniform (List Char) -> Op Ordo (Flat.Uniform (List Char))
cons ch rest = con2 {t = List Char} listCons ch rest

failing "Can't find an implementation for Only STRING Int"
  -- an Int is never a string's object
  intAsString : Flat.Uniform Int -> Op Ordo (Obj STRING)
  intAsString v = Obj.valueObject v

failing "Can't find an implementation for Repr STRING Int"
  -- nor is a string's object an Int
  stringAsInt : Obj STRING -> Op Ordo (Flat.Uniform Int)
  stringAsInt o = Obj.objectValue o

failing "Can't find an implementation for FieldOf (List Char) listCons 0 (List Char)"
  -- a list's head is a character, not its tail
  tailForHead : Con (List Char) listCons -> Op Ordo (Flat.Uniform (List Char))
  tailForHead c = field 0 c

failing "Mismatch between: Char and List Char"
  -- a cell made with its fields the wrong way round
  swapped : Flat.Uniform Char -> Flat.Uniform (List Char) -> Op Ordo (Flat.Uniform (List Char))
  swapped ch rest = con2 {t = List Char} listCons rest ch

failing "Can't find an implementation for ConOf (List Char) (declared 2) ?n"
  -- a list has no third constructor
  noSuchCon : Flat.Uniform (List Char) -> Op Ordo (Maybe (Con (List Char) (declared 2)))
  noSuchCon xs = asCon (declared 2) xs

failing "Can't find an implementation for Immediate String"
  -- a string is an object, not a fixnum
  stringAsFixnum : Flat.Uniform String -> Op Ordo Bits64
  stringAsFixnum s = immediate s

failing "Can't find an implementation for shape CON = Just RAW"
  -- a list's cell holds values the collector follows: no word is stored
  -- in it but through its constructor
  cellWritten : Flat.Uniform (List Char) -> Op Ordo ()
  cellWritten xs = do
    o <- Obj.valueObject {k = CON} xs
    Obj.store64 o 8 0

failing "Can't find an implementation for Num ConId"
  -- a constructor's id is an identity: nothing computes one
  nextCon : ConId
  nextCon = listCons + 1

failing "Name Native.Types.ConId.MkConId is private"
  -- nor is one made of a word
  forgedId : ConId
  forgedId = MkConId 7

-- a pointer to bytes read as the string it may be
asString : Flat.Uniform (Ptr String) -> Op Ordo (Maybe (Obj STRING))
asString p = asKind STRING p

failing "Can't find an implementation for Only PTR (Ptr String)"
  -- a pointer is of two kinds: no value of it is taken for one unread
  unread : Flat.Uniform (Ptr String) -> Op Ordo (Obj PTR)
  unread p = Obj.valueObject p

failing "Can't find an implementation for Repr STRING (Ptr Int)"
  -- only a pointer to bytes may be a string
  intPointer : Flat.Uniform (Ptr Int) -> Op Ordo (Maybe (Obj STRING))
  intPointer p = asKind STRING p

failing "Can't find an implementation for Objects Char"
  -- a character is a fixnum, with no header to read a kind from
  charKind : Flat.Uniform Char -> Op Ordo (Maybe (Obj STRING))
  charKind c = asKind STRING c

failing "Name Native.Support.Obj.MkObj is private"
  -- an object is not made of an address but by `allocate`
  forged : Obj STRING
  forged = MkObj Refl ?address
