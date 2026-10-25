||| A module that defines a function named as one of the escapes: its
||| definition is no use, and is not reported, but a use of it in the same
||| module is, on its line 12.
module OwnEscape

%default total

uncheckedWord : Nat -> Nat
uncheckedWord n = n

again : Nat -> Nat
again n = uncheckedWord n
