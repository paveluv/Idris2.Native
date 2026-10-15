-- The smallest program with output. It compiles and links into a static
-- executable made of the backend's own instruction bytes, with no
-- assembler, linker or C library; `putStrLn` is the prelude's foreign
-- `prim__putStr`, which the runtime implements by the OS service `write`.
-- What the backend does not lower becomes a jump to the abort stub, which
-- prints `idris: unsupported` and exits with status 70, so a program
-- always compiles and fails only on the paths that reach what is missing.
main : IO ()
main = putStrLn "hello"
