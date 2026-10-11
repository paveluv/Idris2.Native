-- Flat functions and the boundary to them: a loop, a sum built and opened,
-- a case whose value is used, and doubles.
--
-- A flat function becomes a machine function on registers, a word or a
-- double each. Ordinary code, `main` here, still calls it by its own name:
-- that name becomes a wrapper, the boundary, which takes each argument
-- apart from the uniform value ordinary code holds into the registers, calls
-- the flat function, and builds the result as ordinary code represents it.
-- A `Bits64` is a fixnum or a boxed integer outside, a word inside; a
-- `Double` is a boxed double outside, a double register inside.
module Main

data Shape = Circle Double | Rect Bits64 Bits64 | Empty

-- A tail call of itself: a loop, which jumps back to the start with the new
-- `acc` and `n`.
%cg native flat Main.sumTo
sumTo : Bits64 -> Bits64 -> Bits64
sumTo acc 0 = acc
sumTo acc n = sumTo (acc + n) (n - 1)

-- A sum built: its tag, then each constructor's fields, the others' zero.
-- A `Shape` takes four registers, the tag, `Circle`'s double and `Rect`'s
-- two words, so `Circle 2.5` is (0, 2.5, 0, 0) and `Rect 3 4` is
-- (1, 0.0, 3, 4). Outside, a `Shape` is an object of its constructor,
-- holding its fields as uniform values, or the one static `Empty`.
%cg native flat Main.grow
grow : Shape -> Shape
grow (Circle r) = Circle (r * 2.0)
grow (Rect w h) = Rect h w
grow Empty = Empty

-- A case whose value the rest uses: a join, as if written
-- `side s = let w = (case s of ...) in w + 1`, where both alternatives
-- continue at the one `w + 1`.
%cg native flat Main.side
side : Shape -> Bits64
side s = (case s of
            Rect w _ => w
            _ => 0) + 1

-- `grow (Rect 3 4)` is `Rect 4 3`, whose side is 5, and `sumTo 0 5` is 15.
-- The test does not run it: it reads the IR of the three functions and
-- their wrappers.
main : IO ()
main = printLn (sumTo 0 (side (grow (Rect 3 4))))
