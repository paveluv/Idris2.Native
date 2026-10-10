-- Flat functions and the boundary to them: a loop, a sum built and opened,
-- a case whose value is used, and doubles.
module Main

data Shape = Circle Double | Rect Bits64 Bits64 | Empty

-- A tail call of itself: a loop.
%cg native flat Main.sumTo
sumTo : Bits64 -> Bits64 -> Bits64
sumTo acc 0 = acc
sumTo acc n = sumTo (acc + n) (n - 1)

-- A sum built: its tag, then each constructor's fields, the others' zero.
%cg native flat Main.grow
grow : Shape -> Shape
grow (Circle r) = Circle (r * 2.0)
grow (Rect w h) = Rect h w
grow Empty = Empty

-- A case whose value the rest uses: a join.
%cg native flat Main.side
side : Shape -> Bits64
side s = (case s of
            Rect w _ => w
            _ => 0) + 1

main : IO ()
main = printLn (sumTo 0 (side (grow (Rect 3 4))))
