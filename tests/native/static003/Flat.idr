-- Constants marked static whose values are constructors with fields,
-- read by flat code. Flat code reads a constant as its value where it
-- holds that value as ordinary code holds it, in one uniform register: so
-- `listed` reads the cells of `primes`, an `Integer` list as ordinary code
-- holds it (`Uniform`), as the address of the first, which the image
-- holds, as if written
--
--   listed _ = MkUniform <the address of the cell 2 :: ...>
--
-- Flat code holds a pair of `Int`s in two registers, not as the object
-- ordinary code reads, so `paired` reads `pair` by calling the constant's
-- flat form, which computes it, as if written
--
--   paired x = let (a, b) = <a call of pair's flat form> in a + b + x
--
-- and ordinary code reads `pair` as its value, the object in the image.
-- Each is compared with the same value made as the program runs. Every
-- code generator prints the same, so the expected output holds the same
-- lines four times: native; Chez; the flat oracle, Chez with each flat
-- function compiled from its flat form; and native under the encoding
-- whose pointers carry a tag.
module Main

import Native.Flat.Uniform
import System

%default covering

%cg native static Main.primes Main.pair
%cg native flat Main.listed Main.paired

-- As if written `primes = MkUniform [2, 3, 5, 7, 1180591620717411303424]`:
-- the cells of the list, the last head the address of a `BIGNUM`, 2^70.
primes : Uniform (List Integer)
primes = MkUniform [2, 3, 5, 7, 2 * 0x200000000000000000]

-- As if written `pair = (42, 5)`: one object of two fixnums.
pair : (Int, Int)
pair = (6 * 7, 5)

listed : Int -> Uniform (List Integer)
listed _ = primes

paired : Int -> Int
paired x = fst pair + snd pair + x

main : IO ()
main = do
  -- 1, which only the running program knows
  n <- pure (the Int (cast (length !getArgs)))
  let made = [2, 3, 5, 7, 0x400000000000000000 * cast n]
  printLn ((listed 0).value, (listed 0).value == made)
  printLn (paired 1, paired 1 == 47 + n)
  printLn (pair, pair == (42 * n, 5))
