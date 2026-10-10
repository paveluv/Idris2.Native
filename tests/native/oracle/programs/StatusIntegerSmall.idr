-- Integer within the fixnum range, on values known only at run time:
-- Euclidean division and remainder with negative operands, shifts, the
-- bitwise operations on negative values, comparisons, casts to and from the
-- fixed-width types and Char, and a case on a constant. The exit status is
-- the number of checks that fail.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
big : Integer -> Integer
big x = x

%noinline
pick : Integer -> Int
pick 5 = 1
pick (-5) = 2
pick _ = 3

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ big 4611686018427387902 + 1 == 4611686018427387903
  , div (big (-7)) 2 == -4, mod (big (-7)) 2 == 1, div (big 7) (-2) == -3, mod (big 7) (-2) == 1
  , div (big 100) (-1) == -100, mod (big 100) (-1) == 0
  , prim__shl_Integer (big 3) 60 == 3458764513820540928, prim__shr_Integer (big (-5)) 1 == -3
  , prim__shr_Integer (big (-5)) 100 == -1, prim__shr_Integer (big 5) 100 == 0
  , prim__and_Integer (big (-12)) (big 10) == 0, prim__or_Integer (big (-12)) (big 10) == -2
  , prim__xor_Integer (big (-12)) (big 10) == -2
  , big (-3) < big 2, big 5 >= big 5, big (-4611686018427387904) < big 4611686018427387903
  , negate (big 4611686018427387903) == -4611686018427387903
  , the Int (cast (big (-5))) == -5, the Bits8 (cast (big (-1))) == 255, the Int8 (cast (big 200)) == -56
  , the Integer (cast (the Bits8 200)) == 200, the Integer (cast (the Int8 (-5))) == -5
  , ord (the Char (cast (big 65))) == 65, ord (the Char (cast (big 55296))) == 0
  , pick (big 5) == 1, pick (big (-5)) == 2, pick (big 6) == 3
  ]

main : IO ()
main = exitCode (sum (map failed checks))
