-- The 64-bit integer types, on values known only at run time: values beyond
-- the fixnum range, which are boxed, and back; wrapping at 64 bits; a box
-- kept in a constructor field; division and remainder, the most negative
-- value by -1 included; shifts by counts within and beyond the width;
-- unsigned order, division and shifts for Bits64; casts among the widths;
-- and a case on a constant beyond the fixnum range. The exit status is the
-- number of checks that fail.
--
-- Under an encoding with fixnums, a 64-bit value is a fixnum when it fits in
-- 63 bits and a boxed integer otherwise, whichever operation made it: the
-- result of each is tagged when it fits and boxed when not.
module Main

import Data.Bits
import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
int : Int -> Int
int x = x

%noinline
i64 : Int64 -> Int64
i64 x = x

%noinline
b64 : Bits64 -> Bits64
b64 x = x

%noinline
keep : List Int -> Int
keep [x] = x
keep _ = 0

%noinline
pick : Int -> Int
pick 4611686018427387905 = 1
pick 1 = 2
pick _ = 3

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ int 4611686018427387903 + 1 == 4611686018427387904
  , int 4611686018427387904 - 1 == 4611686018427387903
  , int 9223372036854775807 + 1 == -9223372036854775808
  , int 3037000500 * 3037000500 == -9223372036709301616
  , keep [int 6917529027641081856] == 6917529027641081856
  , negate (int (-9223372036854775808)) == -9223372036854775808
  , negate (int (-4611686018427387904)) == 4611686018427387904
  , div (int (-9223372036854775807)) 2 == -4611686018427387904
  , mod (int (-7)) 2 == 1, div (int 7) (-2) == -3
  , div (int (-9223372036854775808)) (-1) == -9223372036854775808
  , mod (int (-9223372036854775808)) (-1) == 0
  , prim__shl_Int (int 1) 62 == 4611686018427387904, prim__shl_Int (int 1) 63 == -9223372036854775808
  , prim__shl_Int (int 1) 64 == 0, prim__shr_Int (int (-8)) 64 == -1, prim__shr_Int (int 8) 70 == 0
  , int (-9223372036854775808) < int 9223372036854775807
  , int 4611686018427387904 > int 4611686018427387903
  , int 6917529027641081856 .&. int 4611686018427387904 == 4611686018427387904
  , i64 9223372036854775807 + 1 == -9223372036854775808
  , b64 18446744073709551615 + 1 == 0, b64 0 - 1 == 18446744073709551615
  , b64 18446744073709551615 > b64 1, b64 9223372036854775808 > b64 9223372036854775807
  , b64 4611686018427387904 > b64 4611686018427387903
  , div (b64 18446744073709551615) 10 == 1844674407370955161, mod (b64 18446744073709551615) 10 == 5
  , prim__shr_Bits64 (b64 18446744073709551615) 1 == 9223372036854775807
  , prim__shl_Bits64 (b64 1) 64 == 0, prim__shr_Bits64 (b64 18446744073709551615) 64 == 0
  , the Int (cast (b64 18446744073709551615)) == -1, the Bits64 (cast (int (-1))) == 18446744073709551615
  , the Bits8 (cast (int 4611686018427387905)) == 1, the Int8 (cast (int 200)) == -56
  , the Integer (cast (int (-5))) == -5
  , the Int (cast (the Integer 4611686018427387903)) == 4611686018427387903
  , the Int32 (cast (b64 18446744073709551615)) == -1
  , pick (int 4611686018427387905) == 1, pick (int 1) == 2, pick (int 7) == 3
  ]

main : IO ()
main = exitCode (sum (map failed checks))
