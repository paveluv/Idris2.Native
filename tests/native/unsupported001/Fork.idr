||| A program that reaches a construct the native backend does not lower
||| yet: `fork`, whose foreign function starts a thread, and threads wait
||| for their design. The program still compiles and links, as every program
||| does: what is not lowered becomes the abort stub, which the program
||| reaches only when it gets there. Before it, `Before the fork` is
||| printed; at it, the stub prints which construct it stands for and in
||| which function, and the program exits with status 70. A foreign
||| function the backend does not implement is a function whose whole body
||| is the stub, so the function named is the foreign function itself.
module Fork

%default total

main : IO ()
main = do
  putStrLn "Before the fork"
  ignore (fork (putStrLn "In the thread"))
  putStrLn "After the fork"
