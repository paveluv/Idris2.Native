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

-- lint: allow public-import: a `FunctionTy` reduces through the machine
-- types' Idris types (`Mach.type`), which every module that writes one in
-- a signature needs
import public Native.Mach

import Data.List.Elem

%default total

||| The primitives.
public export
data Primitive
  = ||| The 128-bit product of two words: its high word and its low word.
    Mul128
  | ||| The 128-bit number of a high and a low word divided by a word: its
    ||| quotient and its remainder, of a high word below the divisor, so that
    ||| the quotient is a word.
    Div128
  | ||| A double's 64 bits, as IEEE 754 lays them out, and the double of 64
    ||| bits.
    DoubleBits | BitsDouble

||| A proposition about arguments of the machine types: a type, of each
||| argument in turn.
public export
Requires : List Mach -> Type
Requires [] = Type
Requires (m :: ms) = Mach.type m -> Requires ms

||| A primitive's arrow: the machine types of its arguments, and of its
||| results, in order, and what its arguments must be for the machine to
||| compute it, if anything: a proposition about them, of which a call
||| gives an erased proof.
public export
record Signature where
  constructor MkSignature
  takes : List Mach
  gives : List Mach
  requires : Maybe (Requires takes)

||| Each primitive's signature.
public export
signature : Primitive -> Signature
signature Mul128 = MkSignature [Mach.U64, Mach.U64] [Mach.U64, Mach.U64] Nothing
signature Div128 =
  MkSignature [Mach.U64, Mach.U64, Mach.U64] [Mach.U64, Mach.U64]
    (Just (\high, _, divisor => (high < divisor) = True))
signature DoubleBits = MkSignature [Mach.F64] [Mach.U64] Nothing
signature BitsDouble = MkSignature [Mach.U64] [Mach.F64] Nothing

||| The Idris type of a primitive of the signature: a function of its
||| arguments, then of an erased proof of what it requires of them, if
||| anything, of its results as a tuple, or of its one result, each the
||| Idris type of its machine type.
public export
FunctionTy : Signature -> Type
FunctionTy sig = arrows sig.takes sig.requires
  where
    results : List Mach -> Type
    results [] = ()
    results [m] = Mach.type m
    results (m :: ms) = (Mach.type m, results ms)

    arrows : (ms : List Mach) -> Maybe (Requires ms) -> Type
    arrows [] Nothing = results sig.gives
    arrows [] (Just p) = (0 _ : p) -> results sig.gives
    arrows (m :: ms) r = (x : Mach.type m) -> arrows ms (map (\f => f x) r)

||| Every primitive, once, which the code generator pairs with its own copy,
||| element by element.
public export
allPrimitives : List Primitive
allPrimitives = [Mul128, Div128, DoubleBits, BitsDouble]

||| The list holds every primitive.
complete : (p : Primitive) -> Elem p Primitive.allPrimitives
complete Mul128 = %search
complete Div128 = %search
complete DoubleBits = %search
complete BitsDouble = %search
