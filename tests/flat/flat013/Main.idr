-- A message to a function that takes it as a `String`, from a `case`
-- alternative, in a flat function. A `String` has no layout, so a flat
-- function passes one only as a static argument: a closed term, which a
-- copy of the callee takes in place of its parameter.
--
-- Idris writes a string literal as `fromString "..."`, and reduces that to
-- the literal only for one shorter than ten characters. A longer one stays
-- a call of `fromString`, and in an alternative its dictionary carries the
-- case block's binding of the scrutinee to its pattern:
--
--     fromString String (let t = A x in <FromString String>) "..."
--
-- which names the pattern's variable `x`, a flat one, that the term never
-- uses. The translation drops such a binding before it asks whether the
-- term is closed, so both messages below are static arguments.
--
-- Each call of `fail` is then of a copy of it for its message, of no
-- parameters left, which the oracle gives Chez with one erased parameter:
-- Chez evaluates a definition of no arguments before the program runs,
-- and the copies' crashes would end it before `main`, on branches the
-- program never takes.
module Main

data P = A Bits64 | B

-- a function of a message, not inline, so that a call of it is a call of
-- a copy for its static arguments
fail : String -> Bits64
fail msg = assert_total (idris_crash msg)

%cg native flat classify
classify : P -> Bits64
classify p = case p of
  A x => if x == 0 then fail "short" else x
  B => fail "a message of more than ten characters"

main : IO ()
main = printLn (classify (A 7))
