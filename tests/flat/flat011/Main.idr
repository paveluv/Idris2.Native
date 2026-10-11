-- A flat main that calls generic and higher-order functions, which are not
-- unfolded: each call at static arguments, a dictionary, a function or a
-- lazy value, gets a copy of its callee made for them, with no dictionary
-- and no closure left. A lambda's captured variable is a parameter of the
-- copy, so the two calls of one lambda share a copy.
module Main

interface Shape a where
  area : a -> Bits64

record Square where
  constructor MkSquare
  side : Bits64

record Rect where
  constructor MkRect
  w : Bits64
  h : Bits64

Shape Square where
  area s = s.side * s.side

Shape Rect where
  area r = r.w * r.h

total2 : Shape a => a -> a -> Bits64
total2 x y = area x + area y

applyTwice : (Bits64 -> Bits64) -> Bits64 -> Bits64
applyTwice f x = f (f x)

digits : Bits64 -> IO ()
digits n = if n < 10 then putChar (digit n)
                     else do digits (n `div` 10)
                             putChar (digit (n `mod` 10))
  where
    digit : Bits64 -> Char
    digit d = cast (cast {to = Bits32} d + 48)

orElse : Bits64 -> Lazy Bits64 -> Bits64
orElse x y = if x == 0 then y else x

tick : Bits64 -> IO Bits64
tick n = pure (n + 1)

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
