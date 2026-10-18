||| The types of the native backend's registers (`Ty`).
|||
||| The modules of `Native.Codegen.IRCommon` are the vocabulary the two IRs
||| share: the types of values, the operators, the per-thread areas, the
||| intrinsics, and the link-time numbering of constructors. The located IR
||| (`Native.Codegen.LocatedIR.Program`) and the term IR (`Native.Codegen.TermIR.Program`)
||| both build on them, the term IR without importing the located IR, whose
||| instructions and terminators share their names with the term IR's.
module Native.Codegen.IRCommon.Ty

import Decidable.Equality.Core
import Native.Codegen.Target
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types
import Native.Types.Kind as Types

%default total

||| The type of a register, under the program's encodings. Every value
||| has one of two representations. A raw value is a machine word or double,
||| used where the code knows the value's type. A uniform value, `Val`, is
||| one word that says by itself whether it is a fixnum or a pointer, used
||| where the code location does not know the type: polymorphic fields,
||| closure captures, the arguments and results of polymorphic functions.
||| Idris erases types, so the representation of a uniform slot can come only
||| from the code location or from the word itself; hence the fixnum tag,
||| which tells a fixnum from everything else.
|||
||| `Fix` and `PtrTo k` refine `Val`: the same word, known to be a fixnum or a
||| pointer to an object of kind k. Knowing it is what lets integer
||| operations work on the words directly and memory operations go through
||| the pointer. A `Val` becomes one by `Narrow`, which asserts what the
||| producer knows, and one becomes a `Val` again by `Widen`; neither has
||| code.
|||
||| `Val` and `PtrTo k` are GC-visible: the collector must find them and may
||| move what they point to. `W64`, `F64` and `Fix` are not, since a fixnum
||| points to nothing. This distinction is what the rooting stubs and the
||| continuations' live sets are derived from.
public export
data Ty : Types.Enc -> Type where
  ||| A raw 64-bit word: integers of every width, with narrowing explicit
  ||| (`Ext`), and addresses and header words.
  W64 : Ty enc
  ||| A raw IEEE 754 binary64 double.
  F64 : Ty enc
  ||| A uniform value: one word that is a fixnum, a pointer to an object, or
  ||| the erased value. How each is a word, the fixnum tag included, is the
  ||| value encoding's (`HeapObj.ValEnc`).
  Val : Ty enc
  ||| A `Val` that is a fixnum. Only a value encoding with fixnums has the
  ||| type.
  ||| Integer arithmetic, comparisons and switches take `Fix`es and mean the
  ||| fixnums' values, which the renderings compute on the words.
  Fix : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Ty enc
  ||| A pointer to an object of the kind: the same word as a `Val` that
  ||| points to it.
  PtrTo : Types.Kind -> Ty enc

public export
Eq (Ty enc) where
  W64 == W64 = True
  F64 == F64 = True
  Val == Val = True
  Fix == Fix = True
  PtrTo a == PtrTo b = a == b
  _ == _ = False

||| Two `Fix`es are equal whatever their erased proofs, which are unique.
public export
DecEq (Ty enc) where
  decEq W64 W64 = Yes Refl
  decEq F64 F64 = Yes Refl
  decEq Val Val = Yes Refl
  decEq (Fix {fx = p}) (Fix {fx = q}) = Yes (rewrite HeapObj.ValEnc.fixnumsUnique p q in Refl)
  decEq (PtrTo a) (PtrTo b) = case decEq a b of
    Yes Refl => Yes Refl
    No c => No (\Refl => c Refl)
  decEq W64 F64 = No (\case Refl impossible)
  decEq W64 Val = No (\case Refl impossible)
  decEq W64 Fix = No (\case Refl impossible)
  decEq W64 (PtrTo _) = No (\case Refl impossible)
  decEq F64 W64 = No (\case Refl impossible)
  decEq F64 Val = No (\case Refl impossible)
  decEq F64 Fix = No (\case Refl impossible)
  decEq F64 (PtrTo _) = No (\case Refl impossible)
  decEq Val W64 = No (\case Refl impossible)
  decEq Val F64 = No (\case Refl impossible)
  decEq Val Fix = No (\case Refl impossible)
  decEq Val (PtrTo _) = No (\case Refl impossible)
  decEq Fix W64 = No (\case Refl impossible)
  decEq Fix F64 = No (\case Refl impossible)
  decEq Fix Val = No (\case Refl impossible)
  decEq Fix (PtrTo _) = No (\case Refl impossible)
  decEq (PtrTo _) W64 = No (\case Refl impossible)
  decEq (PtrTo _) F64 = No (\case Refl impossible)
  decEq (PtrTo _) Val = No (\case Refl impossible)
  decEq (PtrTo _) Fix = No (\case Refl impossible)

public export
Show (Ty enc) where
  show W64 = "W64"
  show F64 = "F64"
  show Val = "Val"
  show Fix = "Fix"
  show (PtrTo k) = "Ptr " ++ show k

||| The register class a value of the type crosses a call boundary in.
public export
classOf : Ty enc -> Target.RegClass
classOf F64 = Target.FloatClass
classOf _ = Target.WordClass

||| Whether the collector must find, and may move, what a register holds.
export
gcVisible : Ty enc -> Bool
gcVisible Val = True
gcVisible (PtrTo _) = True
gcVisible _ = False
