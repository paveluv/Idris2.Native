-- Flat functions over doubles: arithmetic, comparisons with a NaN, casts
-- from the integer types and to Int, and a record of two doubles. Ordinary code
-- makes no double itself: it passes on the ones flat functions return. The
-- exit status is the number of checks that fail.
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

record Point where
  constructor MkPoint
  x : Double
  y : Double

%cg native flat Main.point
point : Bits64 -> Bits64 -> Point
point a b = MkPoint (cast a / 2) (cast b * 1.5)

%cg native flat Main.magnitude
magnitude : Double -> Double
magnitude d = if d < 0 then negate d else d

%cg native flat Main.manhattan
manhattan : Point -> Int
manhattan p = cast (magnitude p.x + magnitude p.y)

%cg native flat Main.scaled
scaled : Double -> Point -> Point
scaled k (MkPoint a b) = MkPoint (k * a) (k - b)

%cg native flat Main.half
half : Bits64 -> Double
half n = cast n / 2

%cg native flat Main.truncated
truncated : Double -> Int
truncated d = cast d

-- 1, 2, 4 and 8 for the comparisons a NaN makes true or false as IEEE 754
-- says: NaN /= NaN holds; NaN == NaN, NaN < 1 and NaN >= 1 do not.
%cg native flat Main.nans
nans : Bits8 -> Bits8
nans k = let n = 0.0 / 0.0 in
         (if n == n then 0 else 1) + (if n /= n then 2 else 0)
         + (if n < 1.0 then 0 else 4) + (if n >= 1.0 then 0 else 8) + k

-- Bits64 to double, at and above 2^63, and back through Int.
%cg native flat Main.roundTrip
roundTrip : Bits64 -> Int
roundTrip x = cast (cast {to = Double} x / 4.0)

%cg native flat Main.signedTrip
signedTrip : Int -> Int
signedTrip x = cast (cast {to = Double} x * 2.0)

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ manhattan (point (b64 3) (b64 4)) == 7
  , manhattan (scaled (half (b64 4)) (point (b64 3) (b64 4))) == 7
  , truncated (half (b64 7)) == 3
  , truncated (scaled (half (b64 1)) (point (b64 9) (b64 0))).x == 2
  , nans 0 == 15
  , roundTrip (b64 9223372036854777856) == 2305843009213694464
  , roundTrip (b64 4096) == 1024
  , signedTrip (-21) == -42
  ]

main : IO ()
main = exitCode (sum (map failed checks))
