-- A flat main that calls generic and higher-order functions, which are not
-- unfolded: each call at static arguments, a dictionary, a function or a
-- lazy value, gets a copy of its callee made for them, with no dictionary
-- and no closure left. A lambda's captured variable is a parameter of the
-- copy, so the two calls of one lambda share a copy.
--
-- Only `main` is marked flat. Everything it calls becomes flat because it
-- calls it: a function whose arguments and result are flat gets a flat form
-- of its own, and any other gets a copy for each distinct set of static
-- arguments it is called with. The comments below show each copy as if it
-- had been written by hand in Idris; the dump the test prints names them
-- `Main.{total2:N}`, `Main.{applyTwice:N}` and `Main.{orElse:N}`.
module Main

-- An interface: a call of a function that takes `Shape a =>` passes a
-- dictionary, a record of the instance's methods, which is static.
interface Shape a where
  area : a -> Bits64

record Square where
  constructor MkSquare
  side : Bits64

record Rect where
  constructor MkRect
  w : Bits64
  h : Bits64

-- Each instance's `area` takes and returns flat values, so it gets a flat
-- form of its own, which the copies of `total2` below call.
Shape Square where
  area s = s.side * s.side

Shape Rect where
  area r = r.w * r.h

-- Generic over the interface. It is an ordinary function, not unfolded, so
-- each call from flat code at a known instance gets a copy at that
-- instance's dictionary. `main` calls it at two instances, so there are two
-- copies, as if written:
--
--   total2Square : Square -> Square -> Bits64
--   total2Square x y = area x + area y    -- `area` of `Shape Square`
--
--   total2Rect : Rect -> Rect -> Bits64
--   total2Rect x y = area x + area y      -- `area` of `Shape Rect`
--
-- The dictionary is gone: each `area` is a direct call of that instance's
-- method.
total2 : Shape a => a -> a -> Bits64
total2 x y = area x + area y

-- Higher-order: the function argument is static, so each call gets a copy at
-- the function it passes. `main` passes `\v => v * k + 1`, which refers to
-- `k`, a value known only at run time. The copy takes `k` as an extra
-- parameter, after its own, as if written:
--
--   applyTwiceStep : Bits64 -> Bits64 -> Bits64
--   applyTwiceStep x k = (\v => v * k + 1) ((\v => v * k + 1) x)
--
-- and, with the lambdas applied, which the translation does:
--
--   applyTwiceStep x k = let v = x * k + 1 in v * k + 1
--
-- Because `k` is a parameter rather than part of the copy, both calls in
-- `main` pass the same lambda and share this one copy: `applyTwiceStep 1 k`
-- and `applyTwiceStep 2 k`.
applyTwice : (Bits64 -> Bits64) -> Bits64 -> Bits64
applyTwice f x = f (f x)

-- Its argument and result are flat (`IO ()` is a function of the world, so
-- it adds the world as an argument), so it has a flat form of its own; so do
-- its local `digit`, and the `Bits64` implementations of `<`, `div` and
-- `mod` it calls.
digits : Bits64 -> IO ()
digits n = if n < 10 then putChar (digit n)
                     else do digits (n `div` 10)
                             putChar (digit (n `mod` 10))
  where
    digit : Bits64 -> Char
    digit d = cast (cast {to = Bits32} d + 48)

-- A lazy argument is static too, as an unevaluated term. `main` passes
-- `k * 7`, which refers to `k`, so the copy takes `k` as a parameter, as if
-- written:
--
--   orElseSeven : Bits64 -> Bits64 -> Bits64
--   orElseSeven x k = if x == 0 then k * 7 else x
--
-- The laziness survives: `k * 7` is computed only in the branch that uses
-- it.
orElse : Bits64 -> Lazy Bits64 -> Bits64
orElse x y = if x == 0 then y else x

-- Flat on its own, with a flat form. `main` calls it so that `k` is a value
-- known only at run time, which the copies must take as a parameter.
tick : Bits64 -> IO Bits64
tick n = pure (n + 1)

-- The flat function. Written with `do` over `IO`; the binds unfold, so its
-- form is a sequence of calls threading the world. As if written with the
-- copies above:
--
--   main = do k <- tick 2
--             digits (total2Square (MkSquare k) (MkSquare 4))
--             putChar ' '
--             digits (total2Rect (MkRect k 5) (MkRect 2 2))
--             putChar ' '
--             digits (applyTwiceStep 1 k)
--             putChar ' '
--             digits (applyTwiceStep 2 k)
--             putChar ' '
--             digits (orElseSeven 0 k)
--             putChar '\n'
--
-- With `k = 3` it prints `25 19 13 22 21`, the same under Chez, where it
-- runs as ordinary code, and under the flat oracle, where every function it
-- reaches is compiled from its flat form.
%cg native flat Main.main
main : IO ()
main = do k <- tick 2
          digits (total2 (MkSquare k) (MkSquare 4))
          putChar ' '
          digits (total2 (MkRect k 5) (MkRect 2 2))
          putChar ' '
          digits (applyTwice (\v => v * k + 1) 1)
          putChar ' '
          digits (applyTwice (\v => v * k + 1) 2)
          putChar ' '
          digits (orElse 0 (k * 7))
          putChar '\n'
