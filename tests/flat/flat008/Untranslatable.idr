module Untranslatable

-- Bodies that the flat translation rejects, each with its reason and the
-- chain of calls that reaches it.

-- A value whose type is not flat: the case is on a String.
%cg native flat Untranslatable.parity
parity : Bits64 -> Bits8
parity n = case show n of
             "0" => 0
             _ => 1

-- A function that is not static: which one is chosen at run time, and it is
-- held in a value.
%cg native flat Untranslatable.chosen
chosen : Bits64 -> Bits64
chosen x = case the (Maybe (Bits64 -> Bits64)) (if x == 0 then Nothing else Just (* 2)) of
             Nothing => 0
             Just f => f x

-- A callee whose argument is not flat.
total
sumList : List Bits64 -> Bits64
sumList [] = 0
sumList (x :: xs) = x + sumList xs

%cg native flat Untranslatable.viaList
viaList : Bits64 -> Bits64
viaList x = sumList [x, x]

-- A callee at static arguments: a generic function, which needs a copy.
twice : (a -> a) -> a -> a
twice f x = f (f x)

%cg native flat Untranslatable.viaGeneric
viaGeneric : Bits64 -> Bits64
viaGeneric x = twice (+ 1) x

-- A callee at a lazy argument, which is static only, so it too needs a copy.
orElse : Bits64 -> Lazy Bits64 -> Bits64
orElse x y = if x == 0 then y else x

%cg native flat Untranslatable.viaLazy
viaLazy : Bits64 -> Bits64
viaLazy x = orElse x (x + 1)

-- The chain: a ground callee, flat itself, whose body is not.
lengthOf : Bits64 -> Bits64
lengthOf n = cast (length (show n))

%cg native flat Untranslatable.viaChain
viaChain : Bits64 -> Bits64
viaChain n = lengthOf n + 1

main : IO ()
main = pure ()
