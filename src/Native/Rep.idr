||| How a register holds what it holds (`Rep`): the one list every other
||| description of a register refines.
|||
||| Four types describe one register, each from its own side. `Rep` says
||| what the code generator may do with it: its class, whether the collector
||| scans it, which operations apply. The machine type (`Native.Mach`) says
||| which Idris primitive it holds, the contract's carrier
||| (`Native.Carrier`) what Idris type crosses the boundary in it, and the
||| IR's type (`IRCommon.Ty`) what the IR knows of it under the program's
||| encodings; each says what it is in `Rep`'s terms (its `rep`), and a table
||| from one to another is a composition through `Rep`, never a table of its
||| own.
|||
||| A case of `Rep` exists exactly when the IR gives that kind of register a
||| set of operations of its own. So the integers are one case, `Word`: the
||| IR holds every integer as a word, its narrowing explicit, and the width
||| and sign that tell one integer type from another are the casts'. A byte
||| address and a code address are cases of their own: the IR gives each its
||| own type and operations, and a distinction `Rep` lacked would be lost on
||| the way into the IR. By the same rule `Rep` changes whenever the IR comes
||| to tell two kinds of register apart, so the contract follows the IR's
||| vocabulary: a new type of the IR is a change of the contract.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Rep

import Decidable.Equality.Core

%default total

||| The register class a value crosses a call boundary in: a double in a
||| floating-point register, every other value in a word register. A target
||| maps each class to its registers; the class itself is not the target's.
public export
data RegClass = WordClass | FloatClass

||| How a register holds what it holds.
public export
data Rep
  = ||| A machine word: an integer of any width up to the word's, a `Char`,
    ||| a constructor's tag.
    Word
  | ||| An IEEE 754 double.
    Dbl
  | ||| A value as the ordinary regime holds it (`Flat.Uniform`), opaque to
    ||| flat code: the one rep the collector scans.
    Uniform
  | ||| The address of memory that holds no object: a run of bytes, an area,
    ||| the allocation window. A memory base, which an offset moves.
    ByteAddr
  | ||| The address of code: a closure's entry, which a jump or a call takes.
    CodeAddr

export
Eq Rep where
  Word == Word = True
  Dbl == Dbl = True
  Uniform == Uniform = True
  ByteAddr == ByteAddr = True
  CodeAddr == CodeAddr = True
  _ == _ = False

export
DecEq Rep where
  decEq Word Word = Yes Refl
  decEq Dbl Dbl = Yes Refl
  decEq Uniform Uniform = Yes Refl
  decEq ByteAddr ByteAddr = Yes Refl
  decEq CodeAddr CodeAddr = Yes Refl
  decEq Word Dbl = No (\case Refl impossible)
  decEq Word Uniform = No (\case Refl impossible)
  decEq Word ByteAddr = No (\case Refl impossible)
  decEq Word CodeAddr = No (\case Refl impossible)
  decEq Dbl Word = No (\case Refl impossible)
  decEq Dbl Uniform = No (\case Refl impossible)
  decEq Dbl ByteAddr = No (\case Refl impossible)
  decEq Dbl CodeAddr = No (\case Refl impossible)
  decEq Uniform Word = No (\case Refl impossible)
  decEq Uniform Dbl = No (\case Refl impossible)
  decEq Uniform ByteAddr = No (\case Refl impossible)
  decEq Uniform CodeAddr = No (\case Refl impossible)
  decEq ByteAddr Word = No (\case Refl impossible)
  decEq ByteAddr Dbl = No (\case Refl impossible)
  decEq ByteAddr Uniform = No (\case Refl impossible)
  decEq ByteAddr CodeAddr = No (\case Refl impossible)
  decEq CodeAddr Word = No (\case Refl impossible)
  decEq CodeAddr Dbl = No (\case Refl impossible)
  decEq CodeAddr Uniform = No (\case Refl impossible)
  decEq CodeAddr ByteAddr = No (\case Refl impossible)

export
Show Rep where
  show Word = "Word"
  show Dbl = "Dbl"
  show Uniform = "Uniform"
  show ByteAddr = "ByteAddr"
  show CodeAddr = "CodeAddr"

||| The class a register of the rep crosses a call boundary in.
public export
regClass : Rep -> RegClass
regClass Dbl = FloatClass
regClass _ = WordClass

||| Whether the collector must find, and may move, what a register of the
||| rep holds.
public export
scanned : Rep -> Bool
scanned Uniform = True
scanned _ = False
