-- A mark that names nothing: there is no `missing` in the program. The
-- name is refused as written, when the program is compiled.
module Unknown

%cg native static Unknown.missing

main : IO ()
main = putStrLn "not reached"
