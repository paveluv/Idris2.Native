-- Flat functions that the flat translation translates. The flat oracle
-- compiles each from its flat form, made ordinary again: the output is the
-- same.
import Digits

-- Recursion, with a literal pattern.
%cg native flat Main.sumTo
sumTo : Bits64 -> Bits64 -> Bits64
sumTo acc 0 = acc
sumTo acc n = sumTo (acc + n) (n - 1)

-- A case block.
%cg native flat Main.classify
classify : Bits64 -> Bits8
classify n = case n `mod` 3 of
               0 => 1
               1 => 2
               _ => 3

-- A with block, on a sum.
%cg native flat Main.withy
withy : Maybe Bits64 -> Bits64
withy m with (m)
  withy m | Nothing = 0
  withy m | Just x = x * 2

-- Lets, and a local function that captures an argument.
%cg native flat Main.local
local : Bits64 -> Bits64
local x = let y = x * 2
              z = y + 1 in
              helper z z
  where
    helper : Bits64 -> Bits64 -> Bits64
    helper a b = a * b + x

-- A lambda that is applied, and a function that returns one.
%cg native flat Main.adder
adder : Bits64 -> Bits64 -> Bits64
adder k = \x => (\y => y + k) x

-- Records and a tuple.
record Point where
  constructor MkPoint
  x : Double
  y : Double

%cg native flat Main.dot
dot : Point -> Point -> Double
dot p q = p.x * q.x + p.y * q.y

%cg native flat Main.swap
swap : (Bits64, Bool) -> (Bool, Bits64)
swap (a, b) = (b, a)

-- A main of the flat regime, calling a flat function of another module.
%cg native flat Main.main
main : IO ()
main = do digits (sumTo 0 100)
          putChar ' '
          digits (local 7)
          putChar ' '
          digits (cast (classify 5))
          putChar ' '
          digits (withy (Just 21))
          putChar ' '
          digits (adder 40 2)
          putChar ' '
          digits (cast (dot (MkPoint 1 2) (MkPoint 3 4)))
          putChar ' '
          digits (case swap (1, True) of
                    (b, _) => if b then 1 else 0)
          putChar '\n'
