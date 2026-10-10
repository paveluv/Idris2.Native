-- The shape of each data type a flat form takes or returns, which
-- the directive `dump-flat` writes after the form: how ordinary code represents its
-- values, constructor by constructor.

record Heap where
  constructor MkHeap

-- A record of four fields: an object.
record Mixed where
  constructor MkMixed
  count : Bits8
  scale : Double
  token : Heap
  flag : Bool

-- A newtype: its field.
record Meters where
  constructor MkMeters
  value : Double

data Shape = Circle Double | Rect Bits64 Bits64 | Empty

data Colour = Red | Green | Blue

-- A triple: pairs, which ordinary code represents as objects of one id.
%cg native flat Main.mixed
mixed : Mixed -> (Bits64, Bits64, Bits64)
mixed m = (cast m.count, 2, 3)

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
