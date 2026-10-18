||| The backend's primitives (`Primitive`): operations of the machine that
||| Idris has no primitive for, each a pure function of words, defined in
||| Idris and computed by the native code generator as the instructions it
||| stands for.
|||
||| A primitive is an Idris definition, with a body that is its meaning: a
||| backend that knows nothing of it compiles the body, so a program that
||| uses one runs anywhere, and the native code generator, which knows it,
||| expands each call to its instructions instead, so the body is never
||| compiled there. Each is defined in a module of `Native.Primitive`, by its
||| signature's type (`FunctionTy`), which Idris checks the body against.
||| That type is the one mark of a primitive: the code generator finds the
||| definition by it, checks there is at most one of each, and has the flat
||| translation take a call of it as a call of a primitive, leaving the body
||| alone.
|||
||| Unlike the contract's other entries (`Native.Port` says what they are),
||| a primitive takes no token, since it reads and changes nothing, may
||| give several words, and is the program's as much as the runtime's.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is). It imports nothing
||| from the compiler, so that the runtime and any program may import it.
module Native.Primitive

import Native.Port

import Data.List.Elem

%default total

||| The primitives.
public export
data Primitive
  = ||| The 128-bit product of two words: its high word and its low word.
    Mul128
  | ||| A double's 64 bits, as IEEE 754 lays them out, and the double of 64
    ||| bits.
    DoubleBits | BitsDouble

||| A primitive's arrow: what its arguments carry, and what its results do,
||| in order.
public export
record Signature where
  constructor MkSignature
  takes : List Port.Carrier
  gives : List Port.Carrier

||| Each primitive's signature.
public export
signature : Primitive -> Signature
signature Mul128 = MkSignature [Port.Word, Port.Word] [Port.Word, Port.Word]
signature DoubleBits = MkSignature [Port.Dbl] [Port.Word]
signature BitsDouble = MkSignature [Port.Word] [Port.Dbl]

||| The Idris type of a primitive of the signature: a function of its
||| arguments, of its results as a tuple, or of its one result. A word is a
||| `Bits64`, a signed word an `Int`, a double a `Double`; a primitive
||| carries nothing else, so one that would is not inhabited.
public export
FunctionTy : Signature -> Type
FunctionTy sig = arrows sig.takes
  where
    carried : Port.Carrier -> Type
    carried Port.Word = Bits64
    carried Port.Signed = Int
    carried Port.Dbl = Double
    carried _ = Void

    results : List Port.Carrier -> Type
    results [] = ()
    results [c] = carried c
    results (c :: cs) = (carried c, results cs)

    arrows : List Port.Carrier -> Type
    arrows [] = results sig.gives
    arrows (c :: cs) = carried c -> arrows cs

||| Every primitive, once, which the code generator pairs with its own copy,
||| element by element.
public export
allPrimitives : List Primitive
allPrimitives = [Mul128, DoubleBits, BitsDouble]

||| The list holds every primitive.
complete : (p : Primitive) -> Elem p Primitive.allPrimitives
complete Mul128 = %search
complete DoubleBits = %search
complete BitsDouble = %search
