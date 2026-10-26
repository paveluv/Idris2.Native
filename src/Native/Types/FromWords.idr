||| The type of a maker of an immutable raw object from words (`FromWords`):
||| what marks a function that makes, of the words a function gives at each
||| index, the object of a type, the twin of the pure load's type that reads
||| one (`Types.PureLoad`).
|||
||| The function's own body is its meaning, which every code generator
||| compiles and runs. The mark is a statement besides, which the type's
||| author answers for: the result is the raw object whose payload is
||| exactly the words `f 0`, `f 1`, ..., `f (n - 1)`, none if `n` is not
||| positive. So a compiler that evaluates a program's constants may make
||| that object of the words without running the body, and lay it out as
||| static data. The type asks the representation contract, where the maker
||| is declared, that its type be a `BYTES` always (`Repr.Only`) and
||| immutable (`Repr.Immutable`): no maker of a mutable type may be one,
||| since a static object is never written.
|||
||| The native code generator takes a definition of this type for a maker
||| only in the module of `Native.Types` that defines `a`, which answers for
||| the type's statements, and refuses one in another module of
||| `Native.Types`, or one Idris inlines at each use, whose calls are then
||| its body; outside them, a definition of this type is an ordinary
||| function, whose body is its meaning everywhere.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is).
module Native.Types.FromWords

import Native.Types.Kind
import Native.Types.Repr

%default total

||| A function that makes the object of `a` of so many words, each the
||| function's word at its index.
public export
FromWords : (a : Type) -> {auto 0 only : Repr.Only Kind.BYTES a} ->
            {auto 0 imm : Repr.Immutable a} -> Type
FromWords a = (words : Int) -> (Int -> Bits64) -> a

||| A maker's arguments, as its type has them: the count of words, then the
||| function of each index.
public export
arity : Nat
arity = 2
