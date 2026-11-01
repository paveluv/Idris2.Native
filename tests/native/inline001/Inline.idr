-- Small flat forms taken in place of their calls (`Native.Flat.Inline`).
-- An `Int` comparison in flat code is a call of the Prelude's `>=` at
-- `Int`, whose flat form is the primitive comparison and a case that gives
-- `False` or `True`; a pair's projection is a call of `fst`'s case block,
-- which gives the first of the pair's two registers. Both call nothing and
-- are small, so flat code takes their bodies in place of the calls: in
--
--   inRange lo hi a b acc =
--     if lo >= hi then acc
--     else inRange (lo + 1) hi a b
--            (if lo >= a && lo <= b then snd (lo, acc + 1) else fst (acc, lo))
--
-- the loop compares and projects with no call, and its self tail call is a
-- jump back to its start, so its machine code calls nothing.
module Main

%cg native flat Main.inRange

||| How many of `lo` to `hi - 1` lie between `a` and `b`, counted onto `acc`.
inRange : (lo, hi, a, b, acc : Int) -> Int
inRange lo hi a b acc =
  if lo >= hi then acc
  else inRange (lo + 1) hi a b (if lo >= a && lo <= b then snd (lo, acc + 1) else fst (acc, lo))

-- Not inlined, so the bounds are known only at run time.
%noinline
given : Int -> Int
given x = x

main : IO ()
main = printLn (inRange (given 0) (given 1000) (given 10) (given 19) 0)
