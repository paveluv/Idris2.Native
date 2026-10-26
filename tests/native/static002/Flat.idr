-- Constants marked static, read by flat code: natively each read is the
-- value the code generator computed as it compiled the program, with no
-- call, as if the program had been written with each value in place of
-- the constant's name. The constants are those of the module `Tables`,
-- which this one imports, and one of `Squares`, which `Tables` imports and
-- this one does not, so its flat functions are checked, as the module is
-- built, with the marks of a module they import, and of one they reach.
--
-- Flat code holds a value in registers, so a constant is read so where its
-- type is one flat code holds as ordinary code holds it, in one uniform
-- register (a `Bytes`, a `Uniform a`), or a machine scalar (a `Bits64`, an
-- `Int`, a `Double`). One of another type, such as a `Bool`, flat code
-- reads by calling its flat form, which computes it.
--
-- Each but the erased value is compared with the same value made as the
-- program runs. Every code generator prints the same, so the expected
-- output holds the same lines four times: native; Chez; the flat oracle,
-- Chez with each flat function compiled from its flat form, where a read
-- of a constant is the constant, which Chez computes before `main`; and
-- native under the encoding whose pointers carry a tag.
module Main

import Native.Flat.Uniform
import Native.Types.Bytes
import System
import Tables

%default covering

%cg native flat Main.cube Main.pastLimit Main.stepped Main.scaled Main.pick
%cg native flat Main.unitAt Main.squareAt Main.flagged

-- Word `i` of the cubes: as if written
--
--   cube i = load (<cubes' object> + 8 + 8 * i)
--
-- the object's address (`lea`), then one load; nothing is called, and no
-- function computes the cubes.
cube : Int -> Bits64
cube i = uncheckedWord cubes i 0

-- As if written `pastLimit x = 9223372036854775815 + x`: the word an
-- immediate (`mov`), which no box holds.
pastLimit : Bits64 -> Bits64
pastLimit x = limit + x

-- As if written `stepped x = x + 42`.
stepped : Int -> Int
stepped x = x + step

-- As if written `scaled x = x * 0.25`: the double's bits an immediate too.
scaled : Double -> Double
scaled x = x * ratio

-- One of two `Integer`s, each as ordinary code holds it: as if written
--
--   pick b = if b then <the BIGNUM of 2^70> else <the fixnum 15>
--
-- the BIGNUM's address (`lea`), or the fixnum, an immediate (`mov`): 15 as
-- 2 * 15 + 1, or under tag0 2 * 15.
pick : Bool -> Uniform Integer
pick b = if b then huge else small

-- The erased value, as if written `unitAt _ = MkUniform ()`: its word,
-- an immediate (`mov`): 1, or under tag0 0.
unitAt : Int -> Uniform ()
unitAt _ = unit

-- Word `i` of the squares, a constant marked static in a module this one
-- does not import, `Squares`, reached through the ordinary function
-- `Tables.square`: flat code calls the flat form of `square`, a function
-- it calls, and that form reads the squares as `cube` reads the cubes, as
-- if written
--
--   square i = load (<squares' object> + 8 + 8 * i)
squareAt : Int -> Bits64
squareAt i = square i

-- `x + 1` if the flag is set: as if written
--
--   flagged x = if <a call of flag's flat form> then x + 1 else x
flagged : Int -> Int
flagged x = if flag then x + 1 else x

-- 2^k, by `k` doublings as the program runs.
twoTo : Nat -> Integer
twoTo Z = 1
twoTo (S k) = 2 * twoTo k

main : IO ()
main = do
  -- 8, which only the running program knows, so that what is made from it
  -- below is made as the program runs
  n <- pure (the Int (cast (length !getArgs) + 7))
  let made = generate n (\i => cast (i * i * i))
  let read = map cube [0 .. 7]
  printLn (read, read == map (\i => uncheckedWord made i 0) [0 .. 7])
  printLn (pastLimit 1, pastLimit 1 == 0x8000000000000000 + cast n)
  printLn (stepped 1, stepped 1 == 6 * (n - 1) + 1)
  printLn (scaled 2.0, scaled 2.0 == 2.0 / cast (n - 4))
  let big = (pick True).value
  let fixnum = (pick False).value
  printLn (big, big == twoTo (cast (n + 62)), fixnum, fixnum == cast (2 * n - 1))
  printLn (unitAt 0).value
  let squares = generate n (\i => cast (i * i))
  let readSquares = map squareAt [0 .. 7]
  printLn (readSquares, readSquares == map (\i => uncheckedWord squares i 0) [0 .. 7])
  -- `flag` read by ordinary code too, as its value
  printLn (flagged 1, flagged 1 == n - 6, flag, flag == (n > 7))
