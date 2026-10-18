-- The runtime takes no value for what it is not: each conversion between a
-- value, as ordinary code holds it (`Uniform a`), and an object of the
-- heap asks the evidence of the representation contract
-- (`Native.Types.Represents`), which states, once, how the code generator
-- lays values out. This file typechecks exactly when each `failing` block
-- fails, for the reason it names, and the rest checks.
--
-- The contract's statements, in surface Idris terms:
--
--     Only STRING String               -- every String is a STRING object
--     Only CON (List a)                -- every list is a CON: [] or (::)
--     ConOf (List a) 1 2               -- (::) is constructor 1, of 2 fields
--     FieldOf (List a) 1 0 a           -- its field 0, the head, is an a
--     FieldOf (List a) 1 1 (List a)    -- its field 1, the tail, a list
--     Immediate Char                   -- a Char is held as its code point
--
-- So `fastPack`'s walk down a list of characters reads, with each step
-- checked:
--
--     cell <- asCon 1 xs               -- Just the (::), or Nothing at []
--     h <- field 0 cell                -- a Uniform Char
--     c <- immediate h                 -- its code point
--     t <- field 1 cell                -- a Uniform (List Char)
module Contract

import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape
import Native.Runtime.Ordo
import Native.Support.Obj
import Native.Types.Kind
import Native.Types.Represents

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
  cell <- asCon {t = List Char} 1 xs
  case cell of
    Nothing => pure 0
    Just c => do
      h <- field {f = Char} 0 c
      immediate h

-- a character put in front of a list
cons : Flat.Uniform Char -> Flat.Uniform (List Char) -> Op Ordo (Flat.Uniform (List Char))
cons ch rest = con2 {t = List Char} 1 ch rest

failing "Can't find an implementation for Only STRING Int"
  -- an Int is never a string's object
  intAsString : Flat.Uniform Int -> Op Ordo (Obj STRING)
  intAsString v = Obj.valueObject v

failing "Can't find an implementation for Represents STRING Int"
  -- nor is a string's object an Int
  stringAsInt : Obj STRING -> Op Ordo (Flat.Uniform Int)
  stringAsInt o = Obj.objectValue o

failing "Can't find an implementation for FieldOf (List Char) 1 0 (List Char)"
  -- a list's head is a character, not its tail
  tailForHead : Con (List Char) 1 -> Op Ordo (Flat.Uniform (List Char))
  tailForHead c = field 0 c

failing "Can't find an implementation for FieldOf (List Char) 1 0 (List Char)"
  -- a cell made with its fields the wrong way round
  swapped : Flat.Uniform Char -> Flat.Uniform (List Char) -> Op Ordo (Flat.Uniform (List Char))
  swapped ch rest = con2 {t = List Char} 1 rest ch

failing "Can't find an implementation for IsCon (List Char) 2"
  -- a list has no constructor 2
  noSuchCon : Flat.Uniform (List Char) -> Op Ordo (Maybe (Con (List Char) 2))
  noSuchCon xs = asCon 2 xs

failing "Can't find an implementation for Immediate String"
  -- a string is an object, not a fixnum
  stringAsFixnum : Flat.Uniform String -> Op Ordo Bits64
  stringAsFixnum s = immediate s

failing "Can't find an implementation for shapeOf CON = Just RAW"
  -- a list's cell holds values the collector follows: no word is stored
  -- in it but through its constructor
  cellWritten : Flat.Uniform (List Char) -> Op Ordo ()
  cellWritten xs = do
    o <- Obj.valueObject {k = CON} xs
    Obj.store64 o 8 0

failing "Name Native.Support.Obj.MkObj is private"
  -- an object is not made of an address but by `allocate`
  forged : Obj STRING
  forged = MkObj Refl ?address
