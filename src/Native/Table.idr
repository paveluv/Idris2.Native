||| Tables (`Table`): functions of the integers from `lo` to `hi` that the
||| native code generator computes when it compiles a program, into
||| read-only data, so that a call of one is a load.
|||
||| A table is an Idris definition of type `Table lo hi r`, with a body that
||| is its meaning: a code generator that knows nothing of tables compiles
||| the body, so a program that uses one runs anywhere. The native code
||| generator finds each by that type alone, evaluates the body at every
||| index of the range with Idris's own evaluator, and lays the values out
||| one row after another, a row of the words of `r`; the body is never
||| compiled there, and may compute in any way, `Integer`s included. A call
||| outside the range cannot be written: the index comes with an erased
||| proof that it is inside, which a caller has from a test of it
||| (`with (lo <= k && k <= hi) proof inside`).
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is). It imports nothing
||| from the compiler, so that the runtime and any program may import it.
module Native.Table

%default total

||| A function of the integers from `lo` to `hi`, of a result that flat code
||| holds in registers, each value known when the program is compiled.
public export
Table : (lo, hi : Int) -> (r : Type) -> Type
Table lo hi r = (k : Int) -> (0 inside : (lo <= k && k <= hi) = True) -> r
