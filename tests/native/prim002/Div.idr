-- The backend's primitive `div128`, a 128-bit number divided by a word,
-- on both code generators. Chez compiles its body, which is its meaning:
-- the exact division of the number, as an `Integer`, its high word times
-- 2^64 plus its low word, taken apart into the quotient and the remainder.
-- The native code generator never compiles the body: it computes each
-- call as one `div`, which gives both at once. The two print the same, so
-- the expected output holds the same lines twice.
--
-- The machine's division faults where the quotient does not fit a word,
-- which is where the high word is not below the divisor; so a call of
-- `div128` takes, after the three words, a proof that it is:
--
--   div128 : (high, low, divisor : Bits64) -> (0 _ : (high < divisor) = True) ->
--            (Bits64, Bits64)
--
-- The proof is erased: the compiled call has the three words alone. Where
-- the program does not know it, it asks, as `divide` does here: `with`
-- the comparison, `proof` names the equality the case found.
module Main

import Native.Primitive.Div128

-- A flat function that divides where it may, and gives the high word back
-- where it may not: as if written
--
--   divide : Bits64 -> Bits64 -> Bits64 -> (Bits64, Bits64)
--
-- with the pair's words in registers, the call of `div128` the instruction.
%cg native flat Main.divide
divide : Bits64 -> Bits64 -> Bits64 -> (Bits64, Bits64)
divide high low divisor with (high < divisor) proof below
  _ | True = div128 high low divisor below
  _ | False = (high, low)

-- A flat function that puts the division together again: the quotient
-- times the divisor, plus the remainder, as a word, which is the low word
-- where it divided; where it did not, the high word times the low plus the
-- low.
%cg native flat Main.recombined
recombined : Bits64 -> Bits64 -> Bits64 -> Bits64
recombined high low divisor = case divide high low divisor of
  (q, r) => q * divisor + r

-- The edges: zero, a divisor of one with no high word, a high word one
-- below the divisor (the largest quotient), the largest divisor, ten to
-- the 19th (the divisor of decimal text), a high word not below the
-- divisor, and a divisor of zero, which no high word is below.
cases : List (Bits64, Bits64, Bits64)
cases =
  [ (0, 0, 7), (0, 18446744073709551615, 1), (6, 18446744073709551615, 7)
  , (18446744073709551614, 18446744073709551615, 18446744073709551615)
  , (1234567, 0x123456789ABCDEF0, 10000000000000000000), (5, 5, 5), (0, 3, 0) ]

main : IO ()
main = do
  traverse_ (\(h, l, d) => printLn (divide h l d)) cases
  traverse_ (\(h, l, d) => printLn (recombined h l d)) cases
