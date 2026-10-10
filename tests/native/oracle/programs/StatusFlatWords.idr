-- Flat functions over machine words, reached from ordinary code through
-- the boundary: arithmetic that wraps at each width, signed and unsigned
-- division, shifts, comparisons, casts, and loops. The exit status is the
-- number of checks that fail.
module Main

import Data.So
import System

exitCode : Int -> IO ()
exitCode n = case choose (n == 0) of
  Left _ => exitSuccess
  Right _ => exitWith (ExitFailure n)

%noinline
b8 : Bits8 -> Bits8
b8 x = x

%noinline
b64 : Bits64 -> Bits64
b64 x = x

%noinline
i8 : Int8 -> Int8
i8 x = x

%noinline
i32 : Int32 -> Int32
i32 x = x

%noinline
int : Int -> Int
int x = x

-- A loop: a tail call of the function itself.
%cg native flat Main.sumTo
sumTo : Bits64 -> Bits64 -> Bits64
sumTo acc 0 = acc
sumTo acc n = sumTo (acc + n) (n - 1)

%cg native flat Main.wrap8
wrap8 : Bits8 -> Bits8 -> Bits8
wrap8 a b = a * b + 7

%cg native flat Main.neg8
neg8 : Int8 -> Int8
neg8 x = negate x - 100

%cg native flat Main.divs
divs : Int -> Int -> Int
divs a b = div a b * 1000 + mod a b

%cg native flat Main.divu
divu : Bits64 -> Bits64 -> Bits64
divu a b = div a b + mod a b

%cg native flat Main.shifts
shifts : Bits32 -> Bits32
shifts x = prim__xor_Bits32 (prim__shl_Bits32 x 4) (prim__shr_Bits32 x 3)

%cg native flat Main.signedShift
signedShift : Int32 -> Int32
signedShift x = prim__shr_Int32 x 2

%cg native flat Main.order
order : Int32 -> Int32 -> Bits8
order a b = if a < b then 1 else if a == b then 2 else 3

%cg native flat Main.unsignedOrder
unsignedOrder : Bits64 -> Bits64 -> Bool
unsignedOrder a b = a > b

%cg native flat Main.narrowed
narrowed : Bits64 -> Int16
narrowed x = cast x

%cg native flat Main.widened
widened : Int8 -> Bits64
widened x = cast x

%cg native flat Main.code
code : Int -> Int
code x = ord (chr x)

-- A loop whose step calls other flat functions.
%cg native flat Main.collatz
collatz : Bits64 -> Bits64 -> Bits64
collatz steps 1 = steps
collatz steps n = collatz (steps + 1) (if n `mod` 2 == 0 then n `div` 2 else 3 * n + 1)

failed : Bool -> Int
failed True = 0
failed False = 1

checks : List Bool
checks =
  [ sumTo 0 (b64 100) == 5050
  , wrap8 (b8 20) (b8 13) == 11
  , neg8 (i8 (-128)) == 28
  , divs (int (-7)) (int 2) == -3999
  , divs (int 7) (int (-2)) == -2999
  , divu (b64 18446744073709551615) (b64 10) == 1844674407370955166
  , shifts 4026531855 == 503316721
  , signedShift (i32 (-20)) == -5
  , order (i32 (-5)) (i32 3) == 1, order (i32 3) (i32 3) == 2, order (i32 4) (i32 3) == 3
  , unsignedOrder (b64 18446744073709551615) (b64 1)
  , narrowed (b64 70000) == 4464, narrowed (b64 40000) == -25536
  , widened (i8 (-1)) == 18446744073709551615
  , code (int 65) == 65
  , collatz 0 (b64 27) == 111
  ]

main : IO ()
main = exitCode (sum (map failed checks))
