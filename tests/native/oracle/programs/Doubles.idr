-- Doubles in ordinary code, printed: constants, arithmetic, comparisons,
-- and casts between doubles and every integer type.
--
-- Ordinary code holds a double as a box, an object of one double; each
-- operation takes the doubles out of their boxes, computes as IEEE 754
-- says, and boxes the result:
--
--     x + y, x - y, x * y, x / y, negate x   rounded to the nearest double
--     x < y, x == y, ...                     false where either is NaN, but /=
--     cast {to = Double} n                   the nearest double, ties to even
--     cast {to = Int} x                      truncated toward zero, then
--                                            wrapped to the width, as a cast
--                                            from Integer wraps
--
-- A double that does not fit the integer type is wrapped as its exact
-- truncation would be: 1e19 as an Int is 1e19 - 2^64. NaN and the
-- infinities cast to an integer type are 0, where Chez ends the program, so
-- they are tested elsewhere (native/double001).
module Main

-- the constants: zeros of both signs, the infinities, and NaN, made by
-- dividing; none so small or so large that an operation of two of them is
-- a subnormal, which Chez prints with its mantissa's width (5e-324|1) and
-- the native runtime as its shortest digits
constants : List Double
constants =
  [ 0.0, -0.0, 1.0, -1.5, 0.1, 123456789.125, 1.0e300, -1.0e-100, 1.0 / 0.0, -1.0 / 0.0 ]

nan : Double
nan = 0.0 / 0.0

-- the operations on a pair, each a line: the arithmetic, then the
-- comparisons as 0 or 1
pairLine : (Double, Double) -> String
pairLine (x, y) =
  unwords
    [ show (x + y), show (x - y), show (x * y), show (x / y), show (negate x)
    , show (x < y), show (x <= y), show (x == y), show (x /= y), show (x >= y), show (x > y) ]
  where
    unwords : List String -> String
    unwords [] = ""
    unwords [s] = s
    unwords (s :: ss) = s ++ " " ++ unwords ss

-- finite doubles cast to every integer type: in each range, at the edges,
-- and beyond them, where the exact truncation wraps
finite : List Double
finite =
  [ 0.0, -0.0, 0.5, -0.5, 1.9, -1.9, 127.5, 128.0, -129.0, 255.9, 256.0, 65535.0, 65536.0
  , 2147483647.0, 2147483648.0, -2147483649.0, 4294967296.0, 9007199254740993.0
  , 9223372036854775807.0, -9223372036854775808.0, 1.0e19, -1.0e19, 18446744073709551615.0
  , 1.0e20, -3.0e30, 1.7976931348623157e308 ]

castLine : Double -> String
castLine x =
  joined
    [ show (cast {to = Int} x), show (cast {to = Int8} x), show (cast {to = Int16} x)
    , show (cast {to = Int32} x), show (cast {to = Int64} x), show (cast {to = Bits8} x)
    , show (cast {to = Bits16} x), show (cast {to = Bits32} x), show (cast {to = Bits64} x) ]
  where
    joined : List String -> String
    joined [] = ""
    joined [w] = w
    joined (w :: ws) = w ++ " " ++ joined ws

-- integers of every type as doubles: exact below 2^53, rounded to the
-- nearest above it, ties to even
intLine : Int -> String
intLine n = show (cast {to = Double} n) ++ " " ++ show (cast {to = Double} (cast {to = Bits64} n))
  ++ " " ++ show (cast {to = Double} (cast {to = Int32} n))
  ++ " " ++ show (cast {to = Double} (cast {to = Bits16} n))

ints : List Int
ints =
  [ 0, 1, -1, 9007199254740993, 9007199254740995, -9007199254740993, 9223372036854775807
  , -9223372036854775808, 4611686018427387903, 123456 ]

-- Integers as doubles, the nearest, ties to even, from fixnums and from
-- bignums: around the fixnum boundary, 2^53 + 1 and its neighbours, 2^64 - 1
-- (which rounds up to 2^64), a tie far above 2^53 broken to even, and past
-- the largest double, which is an infinity
integers : List Integer
integers =
  [ 0, -1, 4611686018427387903, 4611686018427387904, -4611686018427387905, 9007199254740993
  , 9007199254740995, 18446744073709551615, -18446744073709551617
  , (9007199254740993 * 1267650600228229401496703205376) + 1267650600228229401496703205376
  , 9007199254740993 * 1267650600228229401496703205376
  , 340282366920938463463374607431768211457, pow2 1024, negate (pow2 1024), pow2 1024 - 1 ]
  where
    pow2 : Nat -> Integer
    pow2 Z = 1
    pow2 (S k) = 2 * pow2 k

-- doubles as Integers, truncated toward zero, exactly
truncations : List Double
truncations =
  [ 0.0, -0.0, 0.99, -0.99, 1.5, -2.5, 4.611686018427388e18, -4.611686018427388e18, 1.0e19
  , -1.0e30, 1.2345678901234567e100, 1.7976931348623157e308, 9007199254740993.0 ]

main : IO ()
main = do
  traverse_ (putStrLn . show) constants
  putStrLn
    (show nan ++ " " ++ show (nan == nan) ++ " " ++ show (nan /= nan) ++ " " ++ show (nan < 1.0))
  traverse_ (putStrLn . pairLine) [(x, y) | x <- constants, y <- constants]
  traverse_ (putStrLn . castLine) (finite ++ map negate finite)
  traverse_ (putStrLn . intLine) ints
  traverse_ (\n => printLn (cast {to = Double} n)) integers
  traverse_ (\x => printLn (cast {to = Integer} x)) truncations
  printLn
    ( cast {to = Double} (the Bits64 18446744073709551615)
    , cast {to = Double} (the Bits64 9223372036854777856) )
