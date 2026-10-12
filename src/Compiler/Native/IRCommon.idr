||| The vocabulary the native backend's two IRs share: the types of values,
||| the operators, the per-thread areas, the intrinsics, and the link-time
||| numbering of constructors. The located IR (`Compiler.Native.LocatedIR`)
||| re-exports it, and the term IR (`Compiler.Native.TermIR`) builds on it
||| without importing the located IR, whose instructions and terminators
||| share their names with the term IR's.
module Compiler.Native.IRCommon

import public Compiler.Native.HeapObject

import Compiler.Native.Target
import Core.Name

%default total

------------------------------------------------------------------------------
-- Types

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
data Ty : Enc -> Type where
  ||| A raw 64-bit word: integers of every width, with narrowing explicit
  ||| (`Ext`), and addresses and header words.
  W64 : Ty enc
  ||| A raw IEEE 754 binary64 double.
  F64 : Ty enc
  ||| A uniform value: one word that is a fixnum, a pointer to an object, or
  ||| the erased value. How each is a word, the fixnum tag included, is the
  ||| heap-object model's (`Compiler.Native.HeapObject`).
  Val : Ty enc
  ||| A `Val` that is a fixnum. Only a value encoding with fixnums has the
  ||| type.
  ||| Integer arithmetic, comparisons and switches take `Fix`es and mean the
  ||| fixnums' values, which the renderings compute on the words.
  Fix : {auto 0 fx : HasFixnums enc.val} -> Ty enc
  ||| A pointer to an object of the kind: the same word as a `Val` that
  ||| points to it.
  PtrTo : Kind -> Ty enc

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
  decEq (Fix {fx = p}) (Fix {fx = q}) = Yes (rewrite fixnumsUnique p q in Refl)
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
classOf : Ty enc -> RegClass
classOf F64 = FloatClass
classOf _ = WordClass

||| Whether the collector must find, and may move, what a register holds.
public export
gcVisible : Ty enc -> Bool
gcVisible Val = True
gcVisible (PtrTo _) = True
gcVisible _ = False

||| Whether the type refines `Val`: the types `Narrow` makes and `Widen` takes.
public export
refinesVal : Ty enc -> Bool
refinesVal Fix = True
refinesVal (PtrTo _) = True
refinesVal _ = False

------------------------------------------------------------------------------
-- Operators

||| Comparison relations on integers; `S` and `U` are signed and unsigned. On
||| `Fix`es a relation compares the fixnums' values, as 64-bit integers; every
||| value encoding with fixnums orders the words as it orders the values, both
||| signed and unsigned, so a rendering compares the words.
public export
data Rel = EqR | NeR | LtS | LeS | GtS | GeS | LtU | LeU | GtU | GeU

||| Integer operations, on `W64`s or on `Fix`es (`Arith`). A shift takes its
||| count as the second operand, below the word's width; `Shr` is logical and
||| `Sar` arithmetic. The divisions truncate toward zero; dividing by zero, or
||| the most negative word by −1 with `DivS` or `RemS`, is undefined, so the
||| producer checks for both first.
public export
data ArithOp = Add | Sub | Mul | And | Or | Xor | Shl | Shr | Sar
             | DivS | DivU | RemS | RemU

public export
Show ArithOp where
  show Add = "Add"
  show Sub = "Sub"
  show Mul = "Mul"
  show And = "And"
  show Or = "Or"
  show Xor = "Xor"
  show Shl = "Shl"
  show Shr = "Shr"
  show Sar = "Sar"
  show DivS = "DivS"
  show DivU = "DivU"
  show RemS = "RemS"
  show RemU = "RemU"

||| `Negate` is two's-complement negation; `Complement` flips every bit.
public export
data UnOp = Negate | Complement

||| Double arithmetic.
public export
data FOp = FAdd | FSub | FMul | FDiv

public export
Show FOp where
  show FAdd = "FAdd"
  show FSub = "FSub"
  show FMul = "FMul"
  show FDiv = "FDiv"

||| Conversions between raw integers and doubles.
public export
data ConvOp
  = ||| A signed `W64` to the `F64` of its value.
    I2F
  | ||| An `F64` to a `W64`, truncated toward zero.
    F2I
  | ||| An `F64`'s 64 bits, reinterpreted as a `W64`.
    FBits
  | ||| A `W64`'s 64 bits, reinterpreted as an `F64`.
    BitsF

||| The narrow widths of `Ext`, `LoadN` and `StoreN`: 8, 16 and 32 bits.
public export
data SubWord = Sub8 | Sub16 | Sub32

||| A sub-word's width in bytes: the unit of a `LoadN` or `StoreN` index.
public export
subWordBytes : SubWord -> Nat
subWordBytes Sub8 = 1
subWordBytes Sub16 = 2
subWordBytes Sub32 = 4

||| The per-thread memory areas the runtime keeps outside the heap. None of
||| them holds objects.
public export
data Area
  = ||| Arguments beyond the target's argument registers, so that no
    ||| argument travels on the machine stack and a tail call of any arity is
    ||| a move of arguments and a jump.
    ARGS
  | ||| The root buffer. Wherever a collection can start, the rendering's
    ||| stub stores the live GC-visible values here, makes the call, and
    ||| reloads them, since they may have moved. The collector reads the
    ||| entries as roots and rewrites the ones it moves. A stub pushes its
    ||| entries above those in use, so the buffer is a stack, and `NROOTS` is
    ||| its top; since only the allocation slow paths of generated code
    ||| collect, at most one stub is active at a time.
    ROOTS
  | ||| The number of entries of `ROOTS` in use.
    NROOTS
  | ||| Extra registers for register allocation; see `Slot`.
    SCRATCH
  | ||| The lowest the machine stack pointer may go in direct code, which
    ||| every direct function checks on entry. Set at start-up.
    STACK_LIMIT
  | ||| The stack pointer at the program's entry, where the system put the
    ||| argument count, the arguments' addresses and the environment's. Set
    ||| at start-up.
    ARGV
  | ||| The runtime's state: the spaces, the limits, what the last collection
    ||| left live. `runtimeWords` words, which the runtime library lays out.
    RUNTIME

||| The words of `RUNTIME`.
public export
runtimeWords : Nat
runtimeWords = 32

||| Operations on machine state that the runtime needs and no instruction
||| expresses. Each is a fixed instruction sequence per target, never a call.
public export
data IntrinsicName
  = ||| The allocation pointer, as a `W64`.
    GetHp
  | ||| Set the allocation pointer from one `W64`.
    SetHp
  | ||| The allocation limit, as a `W64`.
    GetHpLim
  | ||| Set the allocation limit from one `W64`.
    SetHpLim
  | ||| The current continuation, as a `PtrTo CONT` (heap lowering).
    GetK
  | ||| Set the current continuation from one `PtrTo CONT`: how the collector
    ||| publishes a continuation it has moved.
    SetK
  | ||| One system call: a number and up to six `W64` arguments, giving a
    ||| `W64`. A collection never starts in a system call.
    Syscall
  | ||| The machine stack pointer, as a `W64`; for start-up only.
    GetStackPointer
  | ||| Set the machine stack pointer from one `W64`; for start-up only.
    SetStackPointer

public export
Show IntrinsicName where
  show GetHp = "getHp"
  show SetHp = "setHp"
  show GetHpLim = "getHpLim"
  show SetHpLim = "setHpLim"
  show GetK = "getK"
  show SetK = "setK"
  show Syscall = "syscall"
  show GetStackPointer = "getStackPointer"
  show SetStackPointer = "setStackPointer"

------------------------------------------------------------------------------
-- Linking

||| The link-time numbering of constructors: data constructors, by (type,
||| constructor), and type constructors used as values, to their global ids,
||| which a `CON` header carries as its constructor id.
public export
record ConIds where
  constructor MkConIds
  dataCons : List ((Name, Name), Nat)
  typeCons : List (Name, Nat)

public export
noConIds : ConIds
noConIds = MkConIds [] []
