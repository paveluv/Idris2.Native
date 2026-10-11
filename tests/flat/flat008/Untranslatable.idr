module Untranslatable

-- Bodies that the flat translation rejects, each with its reason and the
-- chain of calls that reaches it. Calls at static arguments get copies
-- (flat011); flat012 has the copies that are rejected.
--
-- Each signature here is flat, so the check accepts it; the body is what
-- fails. Every value a flat function computes must be flat, and every
-- function it calls must be flat in turn, whether the call is direct or many
-- calls away: the reason names the chain of calls down to the problem.

-- A value whose type is not flat: the case is on a String, which `show`
-- builds on the heap.
%cg native flat Untranslatable.parity
parity : Bits64 -> Bits8
parity n = case show n of
             "0" => 0
             _ => 1

-- A function that is not static: which one is chosen at run time, and it is
-- held in a value. A function the code names, or a lambda it writes, is
-- static, and its calls reduce or get copies; one inside a `Maybe` that
-- depends on `x` is a closure on the heap.
%cg native flat Untranslatable.chosen
chosen : Bits64 -> Bits64
chosen x = case the (Maybe (Bits64 -> Bits64)) (if x == 0 then Nothing else Just (* 2)) of
             Nothing => 0
             Just f => f x

-- A callee whose argument is not flat: `sumList` takes a `List`, so it has
-- no flat form, and no copy can make one, since a `List` is not static
-- either.
total
sumList : List Bits64 -> Bits64
sumList [] = 0
sumList (x :: xs) = x + sumList xs

%cg native flat Untranslatable.viaList
viaList : Bits64 -> Bits64
viaList x = sumList [x, x]

-- The chain: a callee whose signature is flat, so it gets a flat form of
-- its own, but whose body is not: `length` counts in `Nat`, and its `cast`
-- to `Bits64` goes through an `Integer`.
lengthOf : Bits64 -> Bits64
lengthOf n = cast (length (show n))

%cg native flat Untranslatable.viaChain
viaChain : Bits64 -> Bits64
viaChain n = lengthOf n + 1

main : IO ()
main = pure ()
