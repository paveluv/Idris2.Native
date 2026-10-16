||| The encodings a program is compiled with (`Enc`). How each sort of data
||| that compiled code and the runtime share is laid out in words is a choice
||| made once per compilation: an encoding. A program and its runtime must
||| agree on every one, so the IR, every pass that depends on one, and the
||| headers (`Types.Header`) are indexed by the program's encodings.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is): it imports nothing from the compiler, so that the runtime's own
||| Idris can import it.
module Native.Types.Enc

import Native.Types.BignumEnc
import Native.Types.StringEnc

import Native.HeapObj.ValEnc as HeapObj

%default total

||| The encodings a program is compiled with. Only encodings belong here; a
||| choice that does not change how data is laid out, such as an
||| optimisation, is a setting of the compilation instead.
|||
||| Code that branches on an encoding matches the record, uses `with`, or
||| calls a function of the encoding such as `fixnumTag`: a `case` on a
||| projection does not refine a proof about it, such as
||| `HasFixnums enc.val`.
public export
record Enc where
  constructor MkEnc
  ||| How a uniform value is a word.
  val : HeapObj.ValEnc
  ||| How an integer outside the small range is a `BIGNUM`.
  bignum : BignumEnc
  ||| How a `String` is laid out.
  string : StringEnc

||| The encodings a program is compiled with unless directed otherwise:
||| fixnum tag 1, bignums of 64-bit limbs holding the magnitude, with the
||| sign in the header, and UTF-8 strings.
public export
defaultEnc : Enc
defaultEnc = MkEnc HeapObj.ValEnc.FixnumTag1 (MkBignumEnc BignumEnc.Limb64 BignumEnc.SignMagnitude) StringEnc.Utf8
