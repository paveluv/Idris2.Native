-- NaN and the infinities cast to every integer type, in ordinary code and
-- in a flat function: 0 each, the cast's failure value, where Chez ends the
-- program and the machines answer differently (x86's truncation gives its
-- integer indefinite, the word 2^63; AArch64's saturates).
--
-- A finite double is its exact truncation wrapped to the width, which the
-- oracle's Doubles compares with Chez; a double that is not finite has no
-- truncation, so it is 0 in every type:
--
--     cast {to = Int} (0.0 / 0.0)    = 0
--     cast {to = Bits8} (1.0 / 0.0)  = 0
--     cast {to = Int64} (-1.0 / 0.0) = 0
--
-- and as an Integer, by the bignum's routine, 0 as well.
module Main

import Data.List

-- the doubles that are not finite
special : List Double
special = [0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0]

-- every integer type's cast, in ordinary code
ordinary : Double -> List String
ordinary x =
  [ show (cast {to = Int} x), show (cast {to = Int8} x), show (cast {to = Int16} x)
  , show (cast {to = Int32} x), show (cast {to = Int64} x), show (cast {to = Bits8} x)
  , show (cast {to = Bits16} x), show (cast {to = Bits32} x), show (cast {to = Bits64} x)
  , show (cast {to = Integer} x) ]

-- the same casts in a flat function, as if written
--
--     flatCasts : Double -> (Int, (Int8, (Bits64, Bits32)))
--
-- with each in a register
%cg native flat Main.flatCasts
flatCasts : Double -> (Int, (Int8, (Bits64, Bits32)))
flatCasts x = (cast x, (cast x, (cast x, cast x)))

main : IO ()
main = do
  traverse_ (\x => putStrLn (concat (intersperse " " (ordinary x)))) special
  traverse_ (\x => printLn (flatCasts x)) special
