||| The encodings a program is compiled with (`Enc`). How each sort of data
||| that compiled code and the runtime share is laid out in words is a choice
||| made once per compilation: an encoding. A program and its runtime must
||| agree on every one, so the IR, every pass that depends on one, and the
||| headers (`HeapObj.Header`) are indexed by the program's encodings.
|||
||| Part of the heap-object model, the modules of `HeapObj`: the contract
||| between compiled code and the runtime, not part of either, and so in
||| the namespace of neither.
||| Compiled code writes header words when it allocates and reads constructor
||| ids in a `case`, the runtime's `idris_apply` edits closure headers, and the
||| collector reads kinds, sizes, scanned ranges and continuation layouts.
||| Every bit position and size rule is written down there once, and both
||| sides take it from there. Its modules import nothing from the compiler,
||| so that the runtime's own Idris can import them too.
module HeapObj.Enc

import HeapObj.BignumEnc
import HeapObj.StringEnc
import HeapObj.ValEnc

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
  val : ValEnc
  ||| How an integer outside the small range is a `BIGNUM`.
  bignum : BignumEnc
  ||| How a `String` is laid out.
  string : StringEnc

||| The encodings a program is compiled with unless directed otherwise:
||| fixnum tag 1, bignums of 64-bit limbs holding the magnitude, with the
||| sign in the header, and UTF-8 strings.
public export
defaultEnc : Enc
defaultEnc = MkEnc ValEnc.FixnumTag1 (BignumEnc.MkBignumEnc BignumEnc.Limb64 BignumEnc.SignMagnitude) StringEnc.Utf8
