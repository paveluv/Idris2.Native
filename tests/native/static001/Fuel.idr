-- The steps of an evaluation: each mark is computed in at most 100
-- million, and each constant it reads in as many of its own, once. One
-- that needs more is refused, never computed some other way. A step is a
-- call, a case, an operation, or a word a maker makes.
module Fuel

import Native.Types.Bytes

%cg native static Fuel.huge Fuel.base1024

-- A word for each of 100 million and one: a step each, more than the
-- evaluation allows, so the mark is refused. The maker's steps are
-- counted before its words are made, so the evaluation ends at once,
-- before it holds so many words.
huge : Bytes
huge = generate 100000001 (\i => 0)

-- `n` added to `acc` a turn at a time, in eight steps a turn: two calls,
-- `count`'s own and its comparison's, two cases, and four operations.
count : Int -> Int -> Int
count n acc = if n == 0 then acc else count (n - 1) (acc + 1)

-- About a quarter of a million steps.
base : Int
base = count 30000 0

-- Each of these reads the one before four times. Were each read computed
-- again, each would take four times the steps of the one before, and
-- `base1024` some 250 million, more than the evaluation allows. But the
-- evaluation, as the compiled program does, computes each constant once,
-- in steps of its own, and charges a read of it none: so each of these
-- takes a few steps of its own, and the mark of `base1024` is not
-- refused, as the error shows.
base4 : Int
base4 = base + base + base + base

base16 : Int
base16 = base4 + base4 + base4 + base4

base64 : Int
base64 = base16 + base16 + base16 + base16

base256 : Int
base256 = base64 + base64 + base64 + base64

base1024 : Int
base1024 = base256 + base256 + base256 + base256

main : IO ()
main = printLn (uncheckedWord huge 0 0, base1024)
