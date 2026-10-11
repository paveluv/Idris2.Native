-- A flat function of a library. Its TTC keeps the directive that marks it,
-- and the program that calls it makes its flat form when it is compiled.
module Digits

-- `IO ()` is a function of the world, so a flat function returning it takes
-- the world as one more argument, and a `do` block threads it from one
-- action to the next, as if written
--
--   digits : Bits64 -> PrimIO ()
--   digits n w = if n < 10 then prim__putChar (digit n) w
--                else let MkIORes () w' = digits (n `div` 10) w in
--                         prim__putChar (digit (n `mod` 10)) w'
--
-- `putChar` unfolds, with its dictionary, into the Prelude's private
-- primitive `prim__putChar`, which the Prelude wrote. The local `digit` gets
-- a flat form of its own; as Idris lifts every local function, it takes
-- `digits`'s argument `n` first, though it does not use it.
%cg native flat Digits.digits
export
digits : Bits64 -> IO ()
digits n = if n < 10 then putChar (digit n)
                     else do digits (n `div` 10)
                             putChar (digit (n `mod` 10))
  where
    digit : Bits64 -> Char
    digit d = cast (cast {to = Bits32} d + 48)
