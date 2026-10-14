||| What `remove-unused` takes out: the private functions nothing uses.
module Unused

%default total

-- the module's one mistake
||| Never called.
forgotten : Nat
forgotten = 0

-- A private function something uses stays, and so does one exported.

used : Nat
used = 1

export
answer : Nat
answer = used

-- `main` is what a program starts at: nothing in it calls it, and it stays.

main : IO ()
main = printLn answer
