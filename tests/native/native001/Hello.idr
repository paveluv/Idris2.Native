-- The smallest program with output. The native backend does not lower
-- output yet: what it does not lower becomes a jump to the abort stub, which
-- prints `idris: unsupported` and exits with status 70. So a program always
-- compiles and links, here into a static executable made of the backend's
-- own instruction bytes, with no assembler, linker or C library, and fails
-- only on the paths that reach what is missing.
main : IO ()
main = putStrLn "hello"
