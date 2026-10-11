-- Flat functions that the flat translation translates. The flat oracle
-- compiles each from its flat form, made ordinary again: the output is the
-- same.
--
-- The translation turns a function's clauses into its flat form, in which
-- every value is in registers. What is known where the code is compiled, a
-- dictionary, a lambda that is applied, a case or with block, the binds of a
-- `do` block, is reduced away; what is left are flat values and calls of
-- flat functions. The comments show, for each function, the Idris it
-- amounts to once that is done.
import Digits

-- Recursion, with a literal pattern: a flat function calls itself as any
-- other.
%cg native flat Main.sumTo
sumTo : Bits64 -> Bits64 -> Bits64
sumTo acc 0 = acc
sumTo acc n = sumTo (acc + n) (n - 1)

-- A case block. The case is reduced into the function, and `mod` at
-- `Bits64`, a method of `Integral Bits64`, reached through its dictionary,
-- is a call of that instance's own `mod`, a flat function of its own.
%cg native flat Main.classify
classify : Bits64 -> Bits8
classify n = case n `mod` 3 of
               0 => 1
               1 => 2
               _ => 3

-- A with block, on a sum, reduced into the function, as if written
-- `withy Nothing = 0` and `withy (Just x) = x * 2`.
%cg native flat Main.withy
withy : Maybe Bits64 -> Bits64
withy m with (m)
  withy m | Nothing = 0
  withy m | Just x = x * 2

-- Lets, and a local function that captures an argument. The local
-- function gets a flat form of its own, which takes the argument it
-- captures first, as if written at the top level
--
--   helper : Bits64 -> Bits64 -> Bits64 -> Bits64
--   helper x a b = a * b + x
--
-- and called as `helper x z z`.
%cg native flat Main.local
local : Bits64 -> Bits64
local x = let y = x * 2
              z = y + 1 in
              helper z z
  where
    helper : Bits64 -> Bits64 -> Bits64
    helper a b = a * b + x

-- A lambda that is applied, and a function that returns one. A result that
-- is a function gives the flat function its arguments, and the applied
-- lambdas reduce, as if written
--
--   adder : Bits64 -> Bits64 -> Bits64
--   adder k x = x + k
%cg native flat Main.adder
adder : Bits64 -> Bits64 -> Bits64
adder k = \x => (\y => y + k) x

-- Records and a tuple, whose fields are held in registers: `dot` is as if
-- written with four doubles, `dot px py qx qy = px * qx + py * qy`.
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

-- A main of the flat regime, calling a flat function of another module. Its
-- binds are reduced, and it threads the world as `digits` does, as if
-- written
--
--   main : PrimIO ()
--   main w = let MkIORes () w1 = digits (sumTo 0 100) w
--                MkIORes () w2 = prim__putChar ' ' w1
--                ...
--            in prim__putChar '\n' w13
--
-- The scrutinee of its last `case` is a value of `(Bool, Bits64)`, held in
-- two registers, like any other.
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
