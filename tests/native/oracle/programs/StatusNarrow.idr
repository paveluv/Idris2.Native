-- The narrow integer types, on values known only at run time: wrapping at
-- each width, division and remainder (Euclidean when signed), shifts by
-- counts within and beyond the width, the bitwise operations, comparisons,
-- and casts among them. The exit status is the number of checks that fail.
module Main

import Data.Bits
import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
i8 : Int8 -> Int8
i8 x = x

%noinline
i16 : Int16 -> Int16
i16 x = x

%noinline
i32 : Int32 -> Int32
i32 x = x

%noinline
b8 : Bits8 -> Bits8
b8 x = x

%noinline
b16 : Bits16 -> Bits16
b16 x = x

%noinline
b32 : Bits32 -> Bits32
b32 x = x

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ i8 127 + 1 == -128, i8 (-128) - 1 == 127, i8 100 * 3 == 44
  , i16 32767 + 1 == -32768, i32 2147483647 * 2 == -2
  , b8 255 + 1 == 0, b8 0 - 1 == 255, b16 65535 * 65535 == 1, b32 4294967295 + 2 == 1
  , negate (i8 (-128)) == -128, negate (b8 1) == 255
  , div (i8 (-7)) 2 == -4, mod (i8 (-7)) 2 == 1, div (i8 7) (-2) == -3, mod (i8 7) (-2) == 1
  , div (i8 (-128)) (-1) == -128, mod (i8 (-128)) (-1) == 0
  , div (b8 200) 7 == 28, mod (b8 200) 7 == 4, div (b32 4000000000) 3 == 1333333333
  , prim__shl_Int8 (i8 1) 7 == -128, prim__shl_Int8 (i8 1) 8 == 0
  , prim__shr_Int8 (i8 (-128)) 3 == -16, prim__shr_Int8 (i8 (-128)) 9 == -1
  , prim__shl_Bits8 (b8 255) 1 == 254, prim__shr_Bits8 (b8 255) 3 == 31
  , prim__shr_Bits8 (b8 255) 9 == 0, prim__shl_Bits32 (b32 1) 31 == 2147483648
  , (i8 (-12) .|. 10) == -2, (i16 (-12) .&. 10) == 0, xor (b8 255) 15 == 240
  , b8 200 > b8 100, i8 (-1) < i8 1, b32 4294967295 > b32 0, i32 (-5) <= i32 (-5)
  , the Int16 (cast (i8 (-5))) == -5, the Bits16 (cast (i8 (-5))) == 65531
  , the Int8 (cast (b8 200)) == -56, the Bits8 (cast (i16 300)) == 44
  , the Int32 (cast (b32 4294967295)) == -1, the Int (cast (b8 200)) == 200
  , the Int (cast (i8 (-5))) == -5, the Bits8 (cast (the Int (-1))) == 255
  ]

main : IO ()
main = exitCode (sum (map failed checks))
