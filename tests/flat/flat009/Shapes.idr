-- The shape of each data type a flat form takes or returns, which
-- the directive `dump-flat` writes after the form: how ordinary code represents its
-- values, constructor by constructor.
--
-- Ordinary code, which calls flat functions, holds the same values its own
-- way: a constructor of an enumeration as its tag, an integer; the
-- constructor of a newtype as its field; any other as an object that holds
-- its run-time fields. Where ordinary code calls a flat function, each value
-- is taken apart into registers by its shape, and the result put back
-- together.

record Heap where
  constructor MkHeap

-- A record of four fields: an object. In registers, its fields in turn: a
-- word, a double, none for the token, a word for the `Bool`'s tag.
record Mixed where
  constructor MkMixed
  count : Bits8
  scale : Double
  token : Heap
  flag : Bool

-- A newtype: its field. Ordinary code holds a `Meters` as its `Double`.
record Meters where
  constructor MkMeters
  value : Double

data Shape = Circle Double | Rect Bits64 Bits64 | Empty

-- An enumeration: ordinary code holds each constructor as its tag.
data Colour = Red | Green | Blue

-- A triple: pairs, which ordinary code represents as objects of one id.
%cg native flat Main.mixed
mixed : Mixed -> (Bits64, Bits64, Bits64)
mixed m = (cast m.count, 2, 3)

-- A newtype in, a sum of three constructors out, each an object.
%cg native flat Main.meters
meters : Meters -> Shape
meters (MkMeters m) = Circle m

-- An enumeration, and `Maybe`, whose constructors have ids of their own.
%cg native flat Main.colour
colour : Colour -> Maybe Double
colour Red = Just 1.0
colour _ = Nothing

main : IO ()
main = pure ()
