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
-- `div128` takes, after the three words, a proof that it is, and the
-- machine's remainder is below the divisor, which its result carries a
-- proof of:
--
--   div128 : (high, low, divisor : Bits64) -> (0 _ : (high < divisor) = True) ->
--            Proven (Bits64, Bits64) (\qr => (snd qr < divisor) = True)
--
-- Both proofs are erased: the compiled call has the three words alone, and
-- its result is the pair. Where the program does not know the first, it
-- asks, as `divide` does here: `with` the comparison, `proof` names the
-- equality the case found. Where a division's high word is the remainder
-- of the one before, as in `digits`, the result's proof is the next call's:
-- no division but the first asks.
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
  _ | True = (div128 high low divisor below).value
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

-- The sum of the decimal digits of the number of two words: the number
-- divided by 10 a word at a time from the top, each division's high word
-- the remainder of the one before, below 10 as that division ensures, the
-- first's zero, below 10 by `Refl`: no division asks. A number of two
-- words has at most 39 digits, the steps' bound.
%cg native flat Main.digitSum
digitSum : Bits64 -> Bits64 -> Bits64
digitSum high low = go 39 high low 0
  where
    go : (steps, h, l, acc : Bits64) -> Bits64
    go steps h l acc =
      if steps == 0 || (h == 0 && l == 0) then acc else
        case div128 0 h 10 Refl of
          MkProven (qh, rh) okh => case div128 rh l 10 okh of
            MkProven (ql, rl) _ => go (steps - 1) qh ql (acc + rl)

main : IO ()
main = do
  traverse_ (\(h, l, d) => printLn (divide h l d)) cases
  traverse_ (\(h, l, d) => printLn (recombined h l d)) cases
  traverse_ (\(h, l, _) => printLn (digitSum h l)) cases
