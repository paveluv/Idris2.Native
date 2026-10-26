-- Constants marked static, natively: the code generator computes each as
-- it compiles the program (static001 and the modules `Unlaid` and
-- `Differs` show the marks it refuses), and the image holds its value, so
-- that ordinary code reads it as the value itself, with no call and no
-- cell. It is as if the program had been written with each value in place
-- of the constant's name, such as
--
--   main = do ... printLn (words <the words 0, 1, 4, ..., 49>, ...)
--
-- A number in the fixnum range is an immediate, as a literal is. A big
-- number, a double, a string, a nullary constructor and the words a maker
-- made (`Native.Types.FromWords`) are objects in the image's read-only
-- data, read by their addresses. `()`, which Idris erases, is the erased
-- value.
--
-- Each but `()` is compared with the same value made as the program runs:
-- natively, the evaluation's value against the runtime's. Comparing with
-- Chez alone would not show that they agree: the evaluation computes a
-- primitive as Chez does, and refuses those whose meaning in the program
-- is another, as when it shows a double (the module `Differs`). Every code
-- generator prints the same, so the expected output holds the same lines
-- three times: native, Chez, and native under the encoding whose pointers
-- carry a tag.
module Main

import Native.Types.Bytes
import System

%default covering

%cg native static Main.squares Main.successors Main.big Main.greeting Main.third
%cg native static Main.none Main.unit Main.answer Main.power Main.edge

-- Words a maker made, as if written
--
--   squares = <a BYTES object: its header, then the words 0, 1, 4, ..., 49>
squares : Bytes
squares = generate 8 (\i => cast (i * i))

-- Words made from another static's, which the evaluation reads as the load
-- does: as if written
--
--   successors = <a BYTES object: its header, then the words 1, 2, 5, ..., 50>
successors : Bytes
successors = generate 8 (\i => uncheckedWord squares i 0 + 1)

-- A pattern whose top two bits differ, which no fixnum holds: as if
-- written `big = 9223372036854775813`, which ordinary code holds as an
-- `INT64` box, here one in the image.
big : Bits64
big = 0x8000000000000000 + 5

-- A string the evaluation appends, shows numbers into and casts a
-- character to: as if written
--
--   greeting = "café, -12345678901 and -590295810358705651712"
--
-- a `STRING` object in the image. Idris's own meaning of the cast of 'é'
-- writes it as `show` does, `\233`; the evaluation's is the string of it,
-- as the program's is.
greeting : String
greeting = "caf" ++ cast 'é' ++ ", " ++ show (the Int (-12345678901)) ++ " and "
           ++ show (the Integer (-0x200000000000000000))

-- As if written `third = 0.3333333333333333`: a `DOUBLE` box in the image.
third : Double
third = 1.0 / 3.0

-- As if written `none = Nothing`: the object every `Nothing` is.
none : Maybe Int
none = Nothing

-- As if written `unit = ()`, which Idris erases: the erased value, no
-- object.
unit : ()
unit = ()

-- As if written `answer = 42`: a fixnum, an immediate.
answer : Int
answer = 6 * 7

-- As if written `power = 1180591620717411303424`, 2^70, outside the fixnum
-- range: a `BIGNUM` in the image, its sign and its magnitude's words.
power : Integer
power = 2 * 0x200000000000000000

-- As if written `edge = 4611686018427387904`, 2^62, the first `Int` past
-- the fixnums: an `INT64` box in the image.
edge : Int
edge = 2 * 0x2000000000000000

-- Readers, whose machine code the run script shows: as if written
--
--   table b = if b then <squares' object> else <successors' object>
--   word b = if b then <big's box> else 42
--   wider b = if b then <the BIGNUM of 2^62> else 0
--
-- each alternative one instruction that puts the value in the result's
-- register, then the return: nothing is called. `cast answer` and `cast
-- edge` are folded as the program is compiled, as casts of the literals
-- 42 and 2^62 are; the `Integer` 2^62 is no fixnum either, so the image
-- holds it as a `BIGNUM` of its own, which no constant's value is.
table : Bool -> Bytes
table b = if b then squares else successors

word : Bool -> Bits64
word b = if b then big else cast answer

wider : Bool -> Integer
wider b = if b then cast edge else 0

-- The first eight words.
words : Bytes -> List Bits64
words b = map (\i => uncheckedWord b i 0) [0 .. 7]

-- 2^k, by `k` doublings as the program runs.
twoTo : Nat -> Integer
twoTo Z = 1
twoTo (S k) = 2 * twoTo k

main : IO ()
main = do
  -- 8, which only the running program knows, so that what is made from it
  -- below is made as the program runs
  n <- pure (cast (length !getArgs) + 7)
  let made = generate n (\i => cast (i * i))
  let madeNext = generate n (\i => uncheckedWord made i 0 + 1)
  printLn (words squares, words squares == words made)
  printLn (words successors, words successors == words madeNext)
  printLn (words (table True) == words squares, words (table False) == words successors)
  printLn (big, big == 0x8000000000000000 + cast (n - 3))
  putStrLn greeting
  let three = cast (n - 5)
  printLn (greeting
           == "caf" ++ cast (chr (n + 225)) ++ ", " ++ show (the Int (-12345678909) + n)
              ++ " and " ++ show (negate (twoTo (cast (n + 61)))))
  printLn (third, third == 1.0 / three)
  printLn (none, none == the (Maybe Int) (if n > 0 then Nothing else Just n))
  printLn (unit, answer, answer == 6 * (n - 1))
  printLn (power, power == twoTo (cast (n + 62)))
  printLn (word True, word False)
  printLn (edge, edge == 2 * cast (twoTo (cast (n + 53))))
  printLn (wider True, wider True == twoTo (cast (n + 54)), wider False)
