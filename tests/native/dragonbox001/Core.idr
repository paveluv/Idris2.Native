-- Dragonbox (`Native.Support.Double.Shortest`) against Chez's printer, on
-- Chez: the same Idris source the native runtime runs, compiled by Chez.
-- Chez's `show` of a double is its `number->string`, the shortest digits
-- that read back, as Burger and Dybvig's free format finds them. The two
-- agree but in two ways, each checked here: where a double is exactly
-- halfway between two shortest decimals, Chez takes the upper and
-- Dragonbox the even; and after a subnormal Chez writes `|n`, the bits of
-- its significand, which is not part of the number.
module Main

import Data.List
import Data.String
import Native.Primitive.DoubleBits
import Native.Support.Double.Shortest

-- A decimal: its digits as an integer, and the power of ten they are
-- scaled by.
record Decimal where
  constructor MkDecimal
  digits : Integer
  scale : Integer

-- Chez's text of a positive finite double as a decimal: `1.25e-7` is 125
-- scaled by 10^-9, `1500.0` is 15000 scaled by 10^-1.
chez : String -> Decimal
chez t =
  let number = takeWhile (/= '|') (unpack t)
      (mantissa, rest) = break (== 'e') number
      ex : Integer = case rest of
                       (_ :: ds) => cast (pack ds)
                       [] => 0
      (whole, fraction) = break (== '.') mantissa
      fraction' = drop 1 fraction
  in MkDecimal (cast (pack (whole ++ fraction'))) (ex - cast (length fraction'))

-- Dragonbox's decimal of the double.
ours : Bits64 -> Decimal
ours w =
  case shortest (prim__and_Bits64 w 0xFFFFFFFFFFFFF)
    (prim__and_Bits64 (prim__shr_Bits64 w 52) 0x7FF) of
  (s, e) => MkDecimal (cast s) (cast e)

-- A decimal without the zeros at the end of its digits.
trimmed : Decimal -> Decimal
trimmed (MkDecimal 0 _) = MkDecimal 0 0
trimmed d@(MkDecimal ds sc) = if ds `mod` 10 == 0
  then trimmed (assert_smaller d (MkDecimal (ds `div` 10) (sc + 1))) else d

power : Integer -> Integer -> Integer
power b 0 = 1
power b e = b * power b (assert_smaller e (e - 1))

-- The double of the bits, as an exact fraction: numerator and denominator.
exact : Bits64 -> (Integer, Integer)
exact w =
  let be = cast {to = Integer} (prim__shr_Bits64 w 52)
      f = cast {to = Integer} (prim__and_Bits64 w 0xFFFFFFFFFFFFF)
      (m, e) = if be == 0 then (f, -1074) else (f + 4503599627370496, be - 1075)
  in if e >= 0 then (m * power 2 e, 1) else (m, power 2 (negate e))

-- A decimal as an exact fraction.
fraction : Decimal -> (Integer, Integer)
fraction (MkDecimal ds sc) = if sc >= 0 then (ds * power 10 sc, 1) else (ds, power 10 (negate sc))

-- Whether the double is exactly halfway between the two decimals.
halfway : Bits64 -> Decimal -> Decimal -> Bool
halfway w a b =
  let (vn, vd) = exact w
      (an, ad) = fraction a
      (bn, bd) = fraction b
  in 2 * vn * ad * bd == (an * bd + bn * ad) * vd

-- How many digits a decimal's digits have.
width : Decimal -> Nat
width d = length (show d.digits)

-- One double: the same as Chez, an exact tie whose even digit is ours, or a
-- difference this test does not allow.
data Verdict = Same | Tie | Other String

judge : Bits64 -> Verdict
judge w =
  let d = bitsDouble w
      c = trimmed (chez (show d))
      o = trimmed (ours w)
  in if c.digits == o.digits && c.scale == o.scale then Same
     else if width c == width o && o.digits `mod` 2 == 0 && halfway w c o then Tie
     else Other (show d ++ ": ours " ++ show o.digits ++ "e" ++ show o.scale)

next : Bits64 -> Bits64
next x = x * 6364136223846793005 + 1442695040888963407

-- Random doubles, positive and finite, from a linear congruential sequence.
run : Nat -> Bits64 -> (same, ties : Nat) -> List String -> (Nat, Nat, List String)
run Z _ same ties others = (same, ties, others)
run (S n) x same ties others =
  let w = prim__and_Bits64 x 0x7FFFFFFFFFFFFFFF
  in if prim__shr_Bits64 w 52 == 0x7FF || w == 0 then run n (next x) same ties others
     else case judge w of
            Same => run n (next x) (S same) ties others
            Tie => run n (next x) same (S ties) others
            Other why => run n (next x) same ties (why :: others)

-- The edges: the smallest subnormal and the largest, the smallest normal,
-- the largest double, a power of ten that is no double, 2^53, and doubles
-- whose shortest digits lie at a power of ten.
edges : List Bits64
edges = [1, 0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF, 0x3FB999999999999A,
         0x4340000000000000, 0x44B52D02C7E14AF6, 0x3E7AD7F29ABCAF48, 0x4202A05F20000000]

main : IO ()
main = do
  traverse_ (\w => putStrLn (show (bitsDouble w) ++ ": " ++ case judge w of
                                                          Same => "same"
                                                          Tie => "tie"
                                                          Other why => why)) edges
  let (same, ties, others) = run 200000 2026 0 0 []
  putStrLn
    (show same ++ " the same, " ++ show ties ++ " ties to the even digit, " ++ show (length others)
     ++ " others")
  traverse_ putStrLn (take 5 others)
