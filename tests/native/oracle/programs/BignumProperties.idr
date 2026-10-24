-- Every Integer operation on operands of every size class, printed, so
-- that each result is compared with Chez's: around the fixnum boundary
-- (2^62, which a fixnum stops below), around a word (2^63, 2^64), and of
-- two to six limbs, of both signs.
--
-- An `Integer` in the fixnum range is a fixnum; any other a BIGNUM, its
-- sign and its 64-bit limbs. Generated code adds, subtracts and compares
-- fixnums itself and calls the runtime's routine where an operand is a
-- BIGNUM or the result leaves the range, so each operation here meets both
-- kinds, and results on both sides of the boundary:
--
--     x + y, x - y, x * y        exact
--     div x y, mod x y           Euclidean: mod x y is in [0, |y|)
--     x .&. y, x .|. y, xor x y  on the infinite two's complement form
--     shiftL x n, shiftR x n     arithmetic, shiftR flooring
--     compare x y, negate x      the order, and the negation
--     cast x : Bits64, Int       the integer modulo 2^64, as each type is
--     show x, cast (show x)      decimal text, read back
--
-- A decimal with a point is read only where a double holds the integer
-- exactly: Chez reads one through a double, losing its digits beyond the
-- 17th, where the native runtime truncates the decimal itself.
--
-- The operands come from a fixed generator, so every run, and Chez's, sees
-- the same ones.
module Main

import Data.Bits
import Data.List
import Data.String

-- the operands' generator: a 64-bit linear congruential sequence
next : Bits64 -> Bits64
next s = s * 6364136223846793005 + 1442695040888963407

-- n limbs' worth of the sequence as a natural number, and the seed after
limbs : Nat -> Bits64 -> (Integer, Bits64)
limbs Z s = (0, s)
limbs (S k) s = let (v, s') = limbs k (next s) in (v * 18446744073709551616 + cast s', s')

-- the edges: around the fixnum boundary, around a word, and powers of two
edges : List Integer
edges =
  [ 0, 1, -1, 4611686018427387903, 4611686018427387904, -4611686018427387904
  , -4611686018427387905, 9223372036854775807, 9223372036854775808, -9223372036854775808
  , -9223372036854775809, 18446744073709551615, 18446744073709551616, -18446744073709551616
  , 340282366920938463463374607431768211456, -340282366920938463463374607431768211455 ]

-- random operands of one to six limbs, half of them negative, each made
-- from the seed, the seed after
randoms : Nat -> Bits64 -> List Integer -> List Integer
randoms Z _ acc = acc
randoms (S k) s acc =
  let size = cast (mod (cast {to = Integer} (s `shiftR` 60)) 6) + 1
      (v, s') = limbs size s
      v' = if s' .&. 1 == 0 then v else negate v
  in randoms k (next s') (v' :: acc)

operands : List Integer
operands = edges ++ randoms 24 12345 []

-- a number of limbs, the lowest first
ofLimbs : List Integer -> Integer
ofLimbs = foldr (\l, acc => acc * 18446744073709551616 + l) 0

-- divisions that reach the long division's rare steps, as Hacker's Delight
-- tests its own, at 64-bit limbs: a quotient digit estimated as the base
-- itself, where the dividend's top limb equals the divisor's, and one
-- estimated a digit too large, taken back after its subtraction borrows
divisions : List (Integer, Integer)
divisions =
  [ ( ofLimbs [0, 18446744073709551614, 9223372036854775808]
    , ofLimbs [18446744073709551615, 9223372036854775808] )
  , ( ofLimbs [0, 0, 9223372036854775808, 9223372036854775807]
    , ofLimbs [1, 0, 9223372036854775808] )
  , (ofLimbs [3, 0, 9223372036854775808], ofLimbs [1, 0, 9223372036854775808])
  , ( ofLimbs [0, 0, 9223372036854775808, 9223372036854775807]
    , ofLimbs [18446744073709551615, 0, 9223372036854775808] )
  , ( ofLimbs [0, 18446744073709551615, 18446744073709551614, 9223372036854775807]
    , ofLimbs [18446744073709551615, 9223372036854775807] ) ]

-- a division, its quotient and remainder, and whether they put it back together
divisionLine : (Integer, Integer) -> String
divisionLine (x, y) =
  let q = div x y
      r = mod x y
  in unwords
       [ show q, show r, show (q * y + r == x), show (div (negate x) y)
       , show (mod (negate x) y) ]

-- the operations on a pair, each a line
pairLines : (Integer, Integer) -> List String
pairLines (x, y) =
  [ show (x + y), show (x - y), show (x * y)
  , show (x .&. y), show (x .|. y), show (xor x y), show (compare x y) ]
  ++ (if y == 0 then [] else [show (div x y), show (mod x y)])

-- the operations on one
oneLines : Integer -> List String
oneLines x =
  [ show (negate x), show (cast {to = Bits64} x), show (cast {to = Int} x)
  , show (shiftL x 1), show (shiftL x 63), show (shiftL x 130)
  , show (shiftR x 1), show (shiftR x 64), show (shiftR x 70), show (shiftR x 200)
  , show (cast {to = Integer} (show x) == x), show (abs x) ]
  ++ (if abs x < 9007199254740992 then [show (cast {to = Integer} (show x ++ ".75"))]
      else [])

main : IO ()
main = do
  traverse_ (putStrLn . unwords . oneLines) operands
  traverse_ (putStrLn . unwords . pairLines) [(x, y) | x <- operands, y <- operands]
  traverse_ (putStrLn . divisionLine) divisions
  printLn
    ( cast {to = Integer} "-123456789012345678901234567890"
    , cast {to = Integer} "-4503599627370495.5" )
  printLn (cast {to = Integer} "+98765432109876543210")
  printLn (cast {to = Integer} "12x", cast {to = Integer} "", cast {to = Integer} "-.")
