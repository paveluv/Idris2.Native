-- Copies at static arguments that cannot be flat, each reported with the
-- chain of calls that reaches the problem: a copy whose body is not flat,
-- and copies whose static arguments grow at each recursive call.
module CopyErrors

-- A generic callee whose copy is not flat: it counts a String's characters
-- as an Integer. The call in `viaShow` passes the dictionary of
-- `Show Bits64`, so its copy is as if written
--
--   describeBits64 : Bits64 -> Bits64
--   describeBits64 x = cast (length (show x))
--
-- whose `show` builds a `String`, and whose `length` counts in `Nat`, cast
-- through an `Integer`: the reason follows the chain down to that cast.
describe : Show a => a -> Bits64
describe x = cast (length (show x))

%cg native flat CopyErrors.viaShow
viaShow : Bits64 -> Bits64
viaShow n = describe n

-- Static arguments that grow at each call: a new copy each time. The call
-- in `viaGrow` passes `id` at `Bits64`, and each copy calls `grow` at a new
-- function and a new type, as if written
--
--   grow1 : Bits64 -> Bits64 -> Bits64                -- f = id
--   grow1 0 x = id x
--   grow1 n x = grow2 (n - 1) (x, x)
--
--   grow2 : Bits64 -> (Bits64, Bits64) -> Bits64      -- f = \p => id (fst p)
--   grow2 0 x = id (fst x)
--   grow2 n x = grow3 (n - 1) (x, x)
--
--   grow3 : Bits64 -> ((Bits64, Bits64), (Bits64, Bits64)) -> Bits64
--   ...
--
-- and so on without end. Copies of one function nested eight deep are
-- reported.
grow : (a -> Bits64) -> Bits64 -> a -> Bits64
grow f 0 x = f x
grow f n x = grow (\p => f (fst p)) (n - 1) (x, x)

%cg native flat CopyErrors.viaGrow
viaGrow : Bits64 -> Bits64
viaGrow n = grow id n n

main : IO ()
main = printLn (viaShow 1)
