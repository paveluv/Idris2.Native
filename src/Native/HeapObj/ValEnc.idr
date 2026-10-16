||| How a uniform value is a word: the value encoding (`ValEnc`), one of the
||| program's encodings (`Types.Enc`).
|||
||| A uniform value (`Val` in `Native.Codegen.IRCommon.Ty`) is one word: a
||| fixnum, a pointer to an object, or the erased value. Objects are 8-byte
||| aligned, so an object's address has its low three bits 0, which leaves
||| room for a tag in the word.
|||
||| The erased value stands wherever Idris erased something but a word is
||| still passed (quantity-0 arguments, the `%World` token, types). No code
||| inspects it, and it is never dereferenced, so under an encoding with
||| fixnums it is simply fixnum 0.
|||
||| An integer outside the fixnum range, and under `NoFixnums` every integer,
||| is a boxed object (`INT64`, `BIGNUM`). The renderings carry the encoding
||| out in their `Tag`, `Untag`, `TagOv` and `IfFixnums`, in their arithmetic,
||| comparisons and switches on fixnums, and in the pointer tag of every load
||| and store through a pointer.
|||
||| Part of the heap-object model, the contract between compiled code and
||| the runtime (`HeapObj.Shape` says what it is): it imports nothing from the
||| compiler, so that the runtime's own Idris can import it.
module Native.HeapObj.ValEnc

%default total

||| How a uniform value is a word.
public export
data ValEnc
  = ||| Fixnum tag 1: fixnum n is the word 2n + 1, and a pointer is the
    ||| object's address.
    FixnumTag1
  | ||| Fixnum tag 0: fixnum n is the word 2n, and a pointer is the object's
    ||| address plus 1, so a load or store through it folds the -1 into its
    ||| displacement.
    FixnumTag0
  | ||| No fixnums: every integer in a uniform position is a boxed object,
    ||| and a pointer is the object's address, its low three bits free.
    NoFixnums

public export
Eq ValEnc where
  FixnumTag1 == FixnumTag1 = True
  FixnumTag0 == FixnumTag0 = True
  NoFixnums == NoFixnums = True
  _ == _ = False

public export
Show ValEnc where
  show FixnumTag1 = "FixnumTag1"
  show FixnumTag0 = "FixnumTag0"
  show NoFixnums = "NoFixnums"

||| The value encodings with fixnums: those under which a fixnum, and the
||| IR's tagging instructions, exist.
public export
data HasFixnums : ValEnc -> Type where
  Tag1 : HasFixnums FixnumTag1
  Tag0 : HasFixnums FixnumTag0

public export
Uninhabited (HasFixnums NoFixnums) where
  uninhabited Tag1 impossible
  uninhabited Tag0 impossible

||| An encoding has at most one proof that it has fixnums.
public export
0 fixnumsUnique : (p, q : HasFixnums v) -> p = q
fixnumsUnique Tag1 Tag1 = Refl
fixnumsUnique Tag0 Tag0 = Refl

||| The fixnum tag of an encoding with fixnums: fixnum n is the word 2n plus
||| it.
public export
fixnumTag : (venc : ValEnc) -> {auto 0 fx : HasFixnums venc} -> Integer
fixnumTag FixnumTag1 = 1
fixnumTag FixnumTag0 = 0

||| What a pointer word adds to the object's address.
public export
pointerTag : ValEnc -> Integer
pointerTag FixnumTag1 = 0
pointerTag FixnumTag0 = 1
pointerTag NoFixnums = 0

||| The smallest and the largest fixnum, under either encoding with fixnums.
public export
fixnumMin, fixnumMax : Integer
fixnumMin = -4611686018427387904
fixnumMax = 4611686018427387903

||| Whether an integer is in the fixnum range.
public export
inFixnumRange : Integer -> Bool
inFixnumRange v = v >= fixnumMin && v <= fixnumMax

||| The word of the uniform value that is this integer, where there is one: a
||| fixnum under an encoding with fixnums; under `NoFixnums`, where integers
||| are boxed, only 0, the erased value. An immediate in a `Val` position
||| means the integer, and the rendering takes its word from here.
export
valWord : ValEnc -> Integer -> Maybe Int64
valWord FixnumTag1 v = if inFixnumRange v then Just (cast (2 * v + 1)) else Nothing
valWord FixnumTag0 v = if inFixnumRange v then Just (cast (2 * v)) else Nothing
valWord NoFixnums v = if v == 0 then Just 0 else Nothing

||| The erased value's word: fixnum 0's under an encoding with fixnums, the
||| word 0 under `NoFixnums`.
export
erasedWord : ValEnc -> Int64
erasedWord FixnumTag1 = 1
erasedWord FixnumTag0 = 0
erasedWord NoFixnums = 0

||| Whether a word is a fixnum's.
public export
isFixnumWord : ValEnc -> Int64 -> Bool
isFixnumWord FixnumTag1 w = mod (abs (the Integer (cast w))) 2 == 1
isFixnumWord FixnumTag0 w = mod (abs (the Integer (cast w))) 2 == 0
isFixnumWord NoFixnums _ = False
