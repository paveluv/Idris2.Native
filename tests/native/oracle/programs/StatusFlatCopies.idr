-- Flat functions that call generic and higher-order functions, reached
-- from ordinary code through the boundary. Each call at static arguments,
-- a dictionary or a function, gets a copy of its callee made for them; a
-- lambda's captured variables are the copy's parameters, so one copy serves
-- calls of the same lambda. The exit status is the number of checks that
-- fail.
--
-- The comments show each copy as if it had been written by hand in Idris.
-- A copy takes the call's flat arguments first, then the variables its
-- static arguments capture.
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

interface Shape a where
  area : a -> Bits64

record Square where
  constructor MkSquare
  side : Bits64

record Rect where
  constructor MkRect
  w : Bits64
  h : Bits64

Shape Square where
  area s = s.side * s.side

Shape Rect where
  area r = r.w * r.h

-- Generic over an interface: a copy at each instance. `squares` calls it as
-- if written
--
--   total2Square : Square -> Square -> Bits64
--   total2Square x y = area x + area y        -- `area` of `Shape Square`
--
-- and `rects` the same at `Rect`.
total2 : Shape a => a -> a -> Bits64
total2 x y = area x + area y

-- Higher-order: a copy at each function. Both calls in `twice` pass the
-- same lambda, so they share one copy, which takes the captured `k`:
--
--   applyTwiceStep : Bits64 -> Bits64 -> Bits64
--   applyTwiceStep x k = let v = x * k + 1 in v * k + 1
applyTwice : (Bits64 -> Bits64) -> Bits64 -> Bits64
applyTwice f x = f (f x)

-- Recursion in a copy, at the same static arguments: a loop. The copy for
-- `sums` is as if written
--
--   sumWithTimes : Bits64 -> Bits64 -> Bits64 -> Bits64
--   sumWithTimes acc 0 k = acc
--   sumWithTimes acc n k = sumWithTimes (acc + n * k) (n - 1) k
--
-- whose recursive call is at the same lambda, so it calls the copy itself.
sumWith : (Bits64 -> Bits64) -> Bits64 -> Bits64 -> Bits64
sumWith f acc 0 = acc
sumWith f acc n = sumWith f (acc + f n) (n - 1)

-- A copy that calls another generic function at its own static arguments.
-- `nested` makes two copies, one inside the other:
--
--   bothSquare : Square -> Bits64 -> Bits64
--   bothSquare x k = applyTwicePlus (area x) k   -- `area` of `Shape Square`
--
--   applyTwicePlus : Bits64 -> Bits64 -> Bits64
--   applyTwicePlus x k = (x + k) + k
both : Shape a => (Bits64 -> Bits64) -> a -> Bits64
both f x = applyTwice f (area x)

-- A flat function with function arguments: copied at each call. The call in
-- `composed` passes `k` both as the argument `x` and as the variable its
-- section captures:
--
--   composeTimesPlus : Bits64 -> Bits64 -> Bits64
--   composeTimesPlus x k = (x + 1) * k
--
-- called as `composeTimesPlus k k`.
%cg native flat Main.compose
compose : (Bits64 -> Bits64) -> (Bits64 -> Bits64) -> Bits64 -> Bits64
compose f g x = f (g x)

%cg native flat Main.squares
squares : Bits64 -> Bits64
squares k = total2 (MkSquare k) (MkSquare 4)

%cg native flat Main.rects
rects : Bits64 -> Bits64
rects k = total2 (MkRect k 5) (MkRect 2 2)

%cg native flat Main.twice
twice : Bits64 -> Bits64 -> Bits64
twice k x = applyTwice (\v => v * k + 1) x + applyTwice (\v => v * k + 1) (x + 1)

%cg native flat Main.sums
sums : Bits64 -> Bits64
sums k = sumWith (\i => i * k) 0 10

%cg native flat Main.nested
nested : Bits64 -> Bits64
nested k = both (+ k) (MkSquare k)

%cg native flat Main.composed
composed : Bits64 -> Bits64
composed k = compose (* k) (+ 1) k

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ squares (b64 3) == 25
  , rects (b64 3) == 19
  , twice (b64 3) (b64 1) == 35
  , sums (b64 3) == 165
  , nested (b64 3) == 15
  , composed (b64 3) == 12
  ]

main : IO ()
main = exitCode (sum (map failed checks))
