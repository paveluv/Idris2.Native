-- Fixnum operations across signs, on values known only at run time (the
-- operations are not inlined, so nothing folds them): addition up to the
-- largest fixnum, subtraction, multiplication, negation, the bitwise
-- operations, every comparison, and a case on negative constants. The exit
-- status is the number of checks that fail.
--
-- A fixnum is an `Int` tagged in its word: under the default encoding, n is
-- the word 2n + 1. Each operation computes on the tagged words where it
-- can, `x - 1` as the word minus 2, and checks for overflow.
module Main

import Data.Bits
import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
add : Int -> Int -> Int
add x y = x + y

%noinline
sub : Int -> Int -> Int
sub x y = x - y

%noinline
mul : Int -> Int -> Int
mul x y = x * y

%noinline
neg : Int -> Int
neg x = negate x

%noinline
band : Int -> Int -> Int
band x y = x .&. y

%noinline
bor : Int -> Int -> Int
bor x y = x .|. y

%noinline
bxor : Int -> Int -> Int
bxor x y = xor x y

%noinline
less : Int -> Int -> Bool
less x y = x < y

%noinline
atMost : Int -> Int -> Bool
atMost x y = x <= y

%noinline
greater : Int -> Int -> Bool
greater x y = x > y

%noinline
atLeast : Int -> Int -> Bool
atLeast x y = x >= y

%noinline
same : Int -> Int -> Bool
same x y = x == y

%noinline
classify : Int -> Int
classify (-1) = 1
classify 0 = 2
classify 5 = 3
classify _ = 4

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ add (-5) 3 == -2, add 4611686018427387900 3 == 4611686018427387903
  , sub (-5) 3 == -8, sub 3 (-5) == 8
  , mul (-3) 7 == -21, mul (-4) (-5) == 20, mul 123456789 1000 == 123456789000
  , neg 5 == -5, neg (-7) == 7, neg 0 == 0
  , band (-1) 12 == 12, band (-8) 13 == 8, band 6 3 == 2
  , bor (-8) 3 == -5, bor 4 1 == 5
  , bxor (-1) 5 == -6, bxor 6 3 == 5, bxor (-6) (-1) == 5
  , less (-2) 1, not (less 1 (-2)), atMost (-3) (-3), not (atMost 0 (-1))
  , greater 0 (-1), not (greater (-1) 0), atLeast (-1) (-1), same (-4) (-4), not (same (-1) 1)
  , classify (-1) == 1, classify 0 == 2, classify 5 == 3, classify (-5) == 4
  ]

main : IO ()
main = exitCode (sum (map failed checks))
