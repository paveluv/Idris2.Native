-- Flat functions over records and sums, reached from ordinary code through
-- the boundary, which takes apart and builds each value as ordinary code
-- represents it: a user sum, an enumeration, `Bool`, `Maybe`, `Either`,
-- pairs, a newtype, a record holding a sum, and `IO`. The exit status is
-- the number of checks that fail.
--
-- Inside, a value is its registers: a `Shape` is a tag, `Circle`'s word and
-- `Rect`'s two words, so `Rect 2 3` is (1, 0, 2, 3). Outside, it is as
-- ordinary code holds it: an object of its constructor holding its fields,
-- or, for `Empty`, the one static object. An enumeration such as `Colour`
-- or `Bool` is its tag, a fixnum, outside and a word inside; a newtype such
-- as `Meters` is its field.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
b64 : Bits64 -> Bits64
b64 x = x

data Shape = Circle Bits64 | Rect Bits64 Bits64 | Empty

data Colour = Red | Green | Blue

record Meters where
  constructor MkMeters
  value : Bits64

record Mixed where
  constructor MkMixed
  count : Bits8
  colour : Colour
  flag : Bool
  shape : Shape

%cg native flat Main.area
area : Shape -> Bits64
area (Circle r) = 3 * r * r
area (Rect w h) = w * h
area Empty = 0

%cg native flat Main.grow
grow : Shape -> Shape
grow (Circle r) = Rect r r
grow (Rect w h) = Circle (w + h)
grow Empty = Circle 1

%cg native flat Main.next
next : Colour -> Colour
next Red = Green
next Green = Blue
next Blue = Red

%cg native flat Main.safeDiv
safeDiv : Bits64 -> Bits64 -> Maybe Bits64
safeDiv _ 0 = Nothing
safeDiv a b = Just (div a b)

%cg native flat Main.orZero
orZero : Maybe Bits64 -> Bits64
orZero Nothing = 0
orZero (Just x) = x

%cg native flat Main.swapped
swapped : (Bits64, Bool) -> (Bool, Bits64)
swapped (a, b) = (b, a)

-- A record holding a sum: `Mixed` takes a word for `count`, a word each for
-- the tags of `colour` and `flag`, and `Shape`'s four.
%cg native flat Main.summary
summary : Mixed -> (Bits64, Colour)
summary m = (cast m.count + area m.shape + (if m.flag then 100 else 0), next m.colour)

%cg native flat Main.pick
pick : Bits8 -> Either Bits64 Bool
pick 0 = Left 7
pick _ = Right True

-- A case whose value the rest of the function uses.
%cg native flat Main.sideOf
sideOf : Shape -> Bits64
sideOf s = (case s of
              Circle r => r
              Rect w _ => w
              Empty => 1) + 10

%cg native flat Main.twice
twice : Meters -> Meters
twice (MkMeters m) = MkMeters (2 * m)

-- `IO Bits64` is a function of the world: the flat function takes it as one
-- more argument, which takes no register.
%cg native flat Main.tick
tick : Bits64 -> IO Bits64
tick n = pure (n + 1)

failed : Bool -> Int
failed True = 0
failed False = 1

isRect : Shape -> Bits64 -> Bits64 -> Bool
isRect (Rect w h) a b = w == a && h == b
isRect _ _ _ = False

isCircle : Shape -> Bits64 -> Bool
isCircle (Circle r) a = r == a
isCircle _ _ = False

isRed : Colour -> Bool
isRed Red = True
isRed _ = False

isBlue : Colour -> Bool
isBlue Blue = True
isBlue _ = False

checks : List Bool
checks =
  [ area (Circle (b64 2)) == 12, area (Rect (b64 3) (b64 4)) == 12, area Empty == 0
  , isRect (grow (Circle (b64 5))) 5 5, isCircle (grow (Rect (b64 2) (b64 3))) 5
  , isCircle (grow Empty) 1
  , isBlue (next Green), isRed (next Blue)
  , orZero (safeDiv (b64 17) (b64 5)) == 3, orZero (safeDiv (b64 17) (b64 0)) == 0
  , case safeDiv (b64 9) (b64 3) of
      Just q => q == 3
      Nothing => False
  , case swapped (b64 9, True) of
      (b, n) => b && n == 9
  , case summary (MkMixed 5 Blue True (Rect (b64 2) (b64 3))) of
      (n, c) => n == 111 && isRed c
  , case pick 0 of
      Left n => n == 7
      Right _ => False
  , case pick 1 of
      Left _ => False
      Right b => b
  , sideOf (Rect (b64 4) (b64 9)) == 14, sideOf Empty == 11
  , (twice (MkMeters (b64 21))).value == 42
  ]

main : IO ()
main = do
  n <- tick (b64 41)
  exitCode (sum (map failed checks) + (if n == 42 then 0 else 1))
