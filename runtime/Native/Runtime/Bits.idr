||| Bitwise operations on words, the runtime's own, so that it needs nothing
||| of the libraries but the Prelude. Each is the primitive it is, one
||| instruction in the flat lowering.
|||
||| They have `Data.Bits`' names and fixities, on `Bits64` alone, and the
||| shifts take their count as a word: `Data.Bits`' take a `Fin 64`, a `Nat`
||| at run time, which flat code cannot hold. A program that imports both
||| gets these on `Bits64`, as Idris prefers the definition of the exact
||| type to the interface's, and the same answers.
module Native.Runtime.Bits

%default total

export infixl 8 `shiftL`, `shiftR`
export infixl 7 .&.
export infixl 5 .|.

public export %inline
(.&.) : Bits64 -> Bits64 -> Bits64
(.&.) = prim__and_Bits64

public export %inline
(.|.) : Bits64 -> Bits64 -> Bits64
(.|.) = prim__or_Bits64

||| The word shifted left by `n` bits, zeros coming in.
public export %inline
shiftL : Bits64 -> (n : Bits64) -> Bits64
shiftL = prim__shl_Bits64

||| The word shifted right by `n` bits, zeros coming in.
public export %inline
shiftR : Bits64 -> (n : Bits64) -> Bits64
shiftR = prim__shr_Bits64
