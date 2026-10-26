-- A function is no constant: `twice` takes an argument, so it has no one
-- value to compute.
module Function

%cg native static Function.twice

twice : Int -> Int
twice x = x + x

main : IO ()
main = printLn (twice 21)
