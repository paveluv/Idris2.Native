||| Names of the module written qualified by the module itself. Where the
||| name bare means the same, the qualifier is reported (`self-qualified`):
||| a name of a capital anywhere (`Self.Colour`), one of a small letter on a
||| clause's right-hand side (`Self.base`). In a type, a bare name of a small
||| letter would be a new variable, so there the qualifier names the
||| definition, and is not reported (`AtBase`).
module Self

%default total

public export
data Colour = Red | Green

public export
base : Nat
base = 3

isRed : Self.Colour -> Bool
isRed Red = True
isRed Green = False

next : Nat
next = Self.base + 1

public export
data AtBase : Nat -> Type where
  Here : AtBase Self.base
