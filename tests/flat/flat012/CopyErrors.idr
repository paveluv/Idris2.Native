-- Copies at static arguments that cannot be flat, each reported with the
-- chain of calls that reaches the problem: a copy whose body is not flat,
-- and copies whose static arguments grow at each recursive call.
module CopyErrors

-- A generic callee whose copy is not flat: it counts a String's characters
-- as an Integer.
describe : Show a => a -> Bits64
describe x = cast (length (show x))

%cg native flat CopyErrors.viaShow
viaShow : Bits64 -> Bits64
viaShow n = describe n

-- Static arguments that grow at each call: a new copy each time.
grow : (a -> Bits64) -> Bits64 -> a -> Bits64
grow f 0 x = f x
grow f n x = grow (\p => f (fst p)) (n - 1) (x, x)

%cg native flat CopyErrors.viaGrow
viaGrow : Bits64 -> Bits64
viaGrow n = grow id n n

main : IO ()
main = printLn (viaShow 1)
