||| How an integer outside the small range is a `BIGNUM` (`BignumEnc`), one
||| of the program's encodings (`HeapObj.Enc`): the width of its limbs and
||| how it holds its sign.
|||
||| Part of the heap-object model, the contract between compiled code and
||| the runtime (`HeapObj.Enc` says what it is): it imports nothing from the
||| compiler, so that the runtime's own Idris can import it.
module Native.HeapObj.BignumEnc

%default total

||| How many bits a limb holds. A `BIGNUM`'s limbs are its digits in base 2
||| to that power, least significant first, packed into its words from the
||| low end: one to a word, or two, the lower limb in the word's low half.
public export
data LimbWidth = Limb64 | Limb32

||| How a `BIGNUM` holds its sign.
public export
data BignumSign
  = ||| A sign bit in the header, and the magnitude in the limbs, as in GMP
    ||| and CPython.
    SignMagnitude
  | ||| The limbs hold the value in two's complement, the top limb's top bit
    ||| its sign, as in SBCL.
    TwosComplement

||| How an integer outside the small range is a `BIGNUM`. The small range is
||| the fixnum range under a value encoding with fixnums, and empty under
||| `NoFixnums`, where every integer is a `BIGNUM`.
public export
record BignumEnc where
  constructor MkBignumEnc
  limbWidth : LimbWidth
  sign : BignumSign

||| The bignum encodings whose header holds the sign: those under which a
||| `BignumH` exists.
public export
data SignInHeader : BignumEnc -> Type where
  IsSignMagnitude : SignInHeader (MkBignumEnc w SignMagnitude)

||| Whether a bignum encoding keeps the sign in the header, with the proof
||| that it does.
public export
signInHeader : (b : BignumEnc) -> Maybe (SignInHeader b)
signInHeader (MkBignumEnc _ SignMagnitude) = Just IsSignMagnitude
signInHeader (MkBignumEnc _ TwosComplement) = Nothing

||| The words a `BIGNUM`'s limbs fill for a magnitude, least significant
||| first, none of them a zero at the top: the same under either limb width,
||| since two 32-bit limbs fill a word as one 64-bit limb does.
public export covering
magnitudeWords : Integer -> List Int64
magnitudeWords m =
  if m <= 0 then [] else word (m `mod` 18446744073709551616) :: magnitudeWords (m `div` 18446744073709551616)
  where
    word : Integer -> Int64
    word u = cast (if u >= 9223372036854775808 then u - 18446744073709551616 else u)
