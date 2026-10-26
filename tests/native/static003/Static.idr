-- Constants marked static whose values are constructors with fields:
-- natively the code generator computes each as it compiles the program,
-- and the image holds the value as the objects ordinary code would have
-- made, in its read-only data, so that a read of the constant is the
-- address of its first object, with no call, no cell and nothing
-- allocated (`Held` shows that). It is as if the program had been written
--
--   main = do ... printLn (<the address of the cell 2 :: ...>, ...)
--
-- Each object's fields are words as ordinary code holds them: a fixnum
-- as itself, the erased value as its word, and any other value as the
-- address of its object, another static object, a big number's, a
-- double's or a string's as when a literal is read, or a constructor's
-- of its own. Objects of equal contents are one object, so `counted`,
-- `0 :: primes`, is one cell more, whose tail is the first cell of
-- `primes`.
--
-- Each is compared with the same value made as the program runs, and
-- every code generator prints the same, so the expected output holds the
-- same lines three times: native, Chez, and native under the encoding
-- whose pointers carry a tag.
module Main

import System

%default covering

%cg native static Main.primes Main.counted Main.sample Main.grid

-- 2^k, by `k` doublings.
twoTo : Nat -> Integer
twoTo Z = 1
twoTo (S k) = 2 * twoTo k

-- As if written
--
--   primes = [2, 3, 5, 7, 2305843009213693951, 618970019642690137449562111]
--
-- six cells, `(::)`'s objects, each of its head and its tail: a fixnum or
-- the address of a `BIGNUM` (2^89 - 1, outside the fixnum range), and the
-- address of the next cell, the last's the object every `Nil` is.
primes : List Integer
primes = [2, 3, 5, 7, twoTo 61 - 1, twoTo 89 - 1]

-- As if written `counted = 0 :: <the first cell of primes>`: one cell, of
-- the fixnum 0 and the address of the cells of `primes`.
counted : List Integer
counted = 0 :: primes

-- A record of a field of each kind ordinary code holds.
record Sample where
  constructor MkSample
  ratio : Double
  name : String
  count : Int
  pattern : Bits64
  huge : Integer
  letter : Char
  flag : Bool
  found : Maybe Int
  size : Nat
  done : ()

-- As if written
--
--   sample = MkSample 0.25 "static" (-42) 9223372036854775815
--                     1180591620717411303424 'x' True (Just 9) 7 ()
--
-- one object of ten fields: the address of a `DOUBLE`, of a `STRING`,
-- the fixnum -42, the address of an `INT64` box (a pattern whose top two
-- bits differ), of a `BIGNUM` (2^70), the fixnum of 'x', the fixnum 1
-- (Idris holds a type whose constructors have no fields, `Bool`, as the
-- number of its constructor), the address of `Just`'s object, of the
-- fixnum 9, the fixnum 7 (a `Nat` is an `Integer`), and the erased value
-- (`()`, which Idris erases), the word of the fixnum 0.
sample : Sample
sample = MkSample (1.0 / 4.0) ("sta" ++ "tic") (-6 * 7) (0x8000000000000000 + 7) (twoTo 70) 'x'
                  (2 < 3) (Just (3 * 3)) (3 + 4) ()

-- Lists of lists, as if written
--
--   grid = [<the cells 1 :: 2 :: Nil>, Nil, <the cells 1 :: 2 :: Nil>]
--
-- the first row and the last one the same cells.
grid : List (List Int)
grid = [[1, 2], [], [1, 2]]

-- Reads of `primes`, `counted`, `grid` and `sample`, by which the test
-- finds their objects in the image: each returns the address of its
-- constant's first object, as if written
--
--   primesFrom _ = <the address of the cell 2 :: ...>
primesFrom : Int -> List Integer
primesFrom _ = primes

countedFrom : Int -> List Integer
countedFrom _ = counted

gridFrom : Int -> List (List Int)
gridFrom _ = grid

sampleFrom : Int -> Sample
sampleFrom _ = sample

-- The fields of a sample, in two parts, which `printLn` shows.
parts : Sample -> ((Double, String, Int, Bits64, Integer), (Char, Bool, Maybe Int, Nat, ()))
parts s =
  ((s.ratio, s.name, s.count, s.pattern, s.huge), (s.letter, s.flag, s.found, s.size, s.done))

main : IO ()
main = do
  -- 1, which only the running program knows, so that what is made from
  -- it below is made as the program runs
  n <- pure (length !getArgs)
  let made = [2, 3, 5, 7, twoTo (60 + n) - 1, twoTo (88 + n) - 1]
  printLn (primesFrom 0, primesFrom 0 == made)
  printLn (countedFrom 0, countedFrom 0 == 0 :: made)
  let madeSample = MkSample (1.0 / cast (3 + n)) ("sta" ++ cast (chr (115 + cast n)) ++ "ic")
                     (-42 * cast n) (0x8000000000000000 + cast (6 + n)) (twoTo (69 + n))
                     (chr (119 + cast n)) (n > 0) (Just (cast (8 + n))) (6 + n) ()
  let read = parts (sampleFrom 0)
  printLn (fst read)
  printLn (snd read)
  printLn (fst read == fst (parts madeSample), snd read == snd (parts madeSample))
  printLn (gridFrom 0, gridFrom 0 == [[1, 2], [], [1, cast (1 + n)]])
