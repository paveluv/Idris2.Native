||| The located IR: the native backend's IR after register allocation, the
||| input of the per-target renderings into machine instructions. Producers
||| do not write it: they write the term IR (`Compiler.Native.TermIR`), whose
||| types make its rules hold, and allocation (`Compiler.Native.Allocate`)
||| makes this IR from it, computing every live list:
|||
|||     VMCode   -- lower --+
|||                         +--> term IR -- allocate --> located IR -- render --> machine code
|||     fragment -- lower --+
|||
||| Design rules:
|||
||| * Neutral about continuations. A non-tail call is one terminator that
|||   carries an abstract continuation (`Cont`): where to resume and what is
|||   live there. Nothing in the IR names a continuation register, a
|||   continuation object or a stack frame, so the same IR renders under
|||   either lowering of continuations (`Compiler.Native.Target.Lowering`).
||| * Target-independent. No instruction of any machine appears. Operations
|||   whose machine instructions differ per machine, such as materialising a constant,
|||   comparing and branching, or taking a code address, are IR instructions.
||| * Located. Every register is a `SCRATCH` slot, holding values of one type;
|||   the IR names no machine register, so none the target reserves can
|||   occur. Liveness is in the IR, in the `live` lists of `Cont`,
|||   `AllocObj`, `AllocSized` and `DirectCall`, and in a resume block's
|||   parameters, as the conversion computed it.
|||
||| The IR assumes what every target in scope provides: 64-bit words,
||| little-endian byte order, 8-byte aligned objects, IEEE 754 binary64
||| doubles, and a flat address space. A 32-bit target would change the
||| fixnum width and every offset.
|||
||| The objects the IR allocates and reads, and how a uniform value is a word,
||| are the heap-object model (`Compiler.Native.HeapObject`), which this
||| module re-exports: the IR names kinds, headers and header parts, and
||| never a bit position or a size rule.
|||
||| Some names are chosen to differ from names in modules that a renderer
||| imports alongside this one: `Rel`, `SubWord`, `MemRef` and `BlockLabel`
||| from the x86 assembly ADT's `Cond`, `Width`, `Mem` and `Label`; `PtrTo`,
||| `Negate` and `Complement` from the Prelude's `Ptr`, `Neg` and `Not`.
module Compiler.Native.LocatedIR

import Core.FC
import Core.Name
import public Compiler.Native.HeapObject
import public Compiler.Native.IRCommon
import Compiler.Native.Target
import Data.List

%default total

------------------------------------------------------------------------------
-- Registers

||| A register: word n of the per-thread `SCRATCH` area, with the type of the
||| values it holds. `SCRATCH` behaves as registers: every value lives in a
||| slot, as a C compiler's spilled values live in its stack frame, but there
||| is one fixed area per thread rather than one per frame. That works
||| because nothing in it survives a call: `SCRATCH` is dead across every
||| call, tail call and return, and every direct call. A value needed after
||| a call is in that call's `live` list, and the rendering keeps it
||| elsewhere until the call is over; so the collector never scans
||| `SCRATCH`. The type travels with every occurrence, because the rendering
||| reads it, to tell the GC-visible members of a `live` list from the raw
||| ones, among others.
public export
data Reg : Enc -> Type where
  Slot : (n : Nat) -> Ty enc -> Reg enc

public export
regTy : Reg enc -> Ty enc
regTy (Slot _ t) = t

||| The slot's number: the register's identity.
public export
slotOf : Reg enc -> Nat
slotOf (Slot n _) = n

public export
Show (Reg enc) where
  show (Slot n t) = "slot" ++ show n ++ ":" ++ show t

------------------------------------------------------------------------------
-- Operands

||| A register, or an immediate: a constant written into the instruction
||| (`Imm`, shown as `#i`). An immediate is allowed wherever the target
||| can encode it or the rendering will materialise it into a register: the
||| IR does not know instruction encodings. Where the instruction expects a `Val` or a
||| `Fix`, the immediate is the integer, and the rendering takes its word from
||| `valWord` in `Compiler.Native.HeapObject`: `#1` is fixnum 1 and `#0`
||| fixnum 0, which as a `Val` is also the erased value, under every value
||| encoding.
public export
data Operand : Enc -> Type where
  R : Reg enc -> Operand enc
  Imm : Int64 -> Operand enc

public export
Show (Operand enc) where
  show (R r) = show r
  show (Imm i) = "#" ++ show i

public export
opRegs : Operand enc -> List (Reg enc)
opRegs (R r) = [r]
opRegs (Imm _) = []

||| A memory operand: a base register, an optional index register, and a
||| constant byte offset. The base is a `PtrTo k` or a `W64`, such as an area's
||| address or the allocation pointer, never a `Val`, which may be a fixnum.
||| The index, a `W64`, counts units of the access's width: words for `Load`
||| and `Store`, the sub-word's bytes for `LoadN` and `StoreN`. So element `i`
||| of an `ARRAY` is at `MkMemRef p (Just i) 8`.
|||
||| Every target addresses a base plus an offset, or a base plus an index
||| scaled by the access's width, in one instruction. A rendering that computes
||| part of an address does so within the instruction, so no address outlives
||| it: an interior pointer never meets a collection.
public export
record MemRef (enc : Enc) where
  constructor MkMemRef
  base : Reg enc
  index : Maybe (Reg enc)
  offset : Int

||| A block's name within its function.
public export
BlockLabel : Type
BlockLabel = Nat

------------------------------------------------------------------------------
-- Instructions

||| An instruction. Each defines at most one register, its destination,
||| which comes first. The types stated here are the term's
||| (`Compiler.Native.TermIR`), which the conversion keeps.
public export
data Instr : Enc -> Type where
  ||| A constant, into a `W64`, a `Val` or a `Fix`. Into a `W64` it is the
  ||| word itself. Into a `Val` or a `Fix` it is the integer, and the
  ||| rendering turns it into the value encoding's word (`valWord` in
  ||| `Compiler.Native.HeapObject`), so that the IR is the same under every
  ||| value encoding; as a `Val`, 0 is also the erased value. No constant is a
  ||| pointer.
  Const      : Reg enc -> Int64 -> Instr enc
  ||| A double constant, into an `F64`.
  FConst     : Reg enc -> Double -> Instr enc
  ||| The entry address of a function of this program, into a `W64`: a
  ||| closure's code pointer.
  CodeAddr   : Reg enc -> Name -> Instr enc
  ||| The address of a static object of this program, into a `Val`, or into a
  ||| `PtrTo k` of the static's kind.
  StaticAddr : Reg enc -> Name -> Instr enc
  ||| The address of a per-thread area, into a `W64`.
  AreaAddr   : Reg enc -> Area -> Instr enc
  ||| Integer arithmetic: the operands and the result are all `W64`s, or all
  ||| `Fix`es. On `Fix`es it is the operation on the fixnums' values, which
  ||| the producer guarantees is in the fixnum range, and the rendering
  ||| computes it on the words, without untagging where the value encoding has
  ||| an identity for it. There is no arithmetic on `Val`s: a `Val` is narrowed
  ||| to a `Fix` first.
  Arith      : ArithOp -> Reg enc -> Operand enc -> Operand enc -> Instr enc
  ||| Negation or complement of a `W64`.
  Unary      : UnOp -> Reg enc -> Reg enc -> Instr enc
  ||| `Add`, `Sub` or `Mul`, with the operand types of `Arith`, then a branch
  ||| to the label if the result does not fit: in 64 signed bits for `W64`s,
  ||| in the fixnum range for `Fix`es, which is the fixnum fast path. The
  ||| label is a successor of the block at this instruction, not at the
  ||| block's end.
  ArithOv    : ArithOp -> Reg enc -> Operand enc -> Operand enc -> BlockLabel -> Instr enc
  ||| Narrow a `W64` to the width, then sign- or zero-extend it back to 64
  ||| bits.
  Ext        : SubWord -> (signed : Bool) -> Reg enc -> Reg enc -> Instr enc
  ||| Double arithmetic on `F64`s.
  FArith     : FOp -> Reg enc -> Reg enc -> Reg enc -> Instr enc
  ||| Double negation.
  FNeg       : Reg enc -> Reg enc -> Instr enc
  ||| Compare two `F64`s; the destination, a `W64`, is 1 or 0.
  FCmp       : Rel -> Reg enc -> Reg enc -> Reg enc -> Instr enc
  ||| Convert between a `W64` and an `F64`.
  Convert    : ConvOp -> Reg enc -> Reg enc -> Instr enc
  ||| Compare two integers; the destination, a `W64`, is 1 or 0. The operands
  ||| are both `W64`s or both `Fix`es, compared as `Rel` says; a comparison
  ||| never makes a value.
  Cmp        : Rel -> Reg enc -> Operand enc -> Operand enc -> Instr enc
  ||| Load a word of the given type.
  Load       : Ty enc -> Reg enc -> MemRef enc -> Instr enc
  ||| Store a register of the given type.
  Store      : Ty enc -> MemRef enc -> Reg enc -> Instr enc
  ||| Load 8, 16 or 32 bits into a `W64`, zero- or sign-extended: the bytes
  ||| of strings and buffers, the limbs of bignums.
  LoadN      : SubWord -> (signed : Bool) -> Reg enc -> MemRef enc -> Instr enc
  ||| Store the low 8, 16 or 32 bits of a `W64`.
  StoreN     : SubWord -> MemRef enc -> Reg enc -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`. The producer guarantees that the
  ||| value is in the fixnum range.
  Tag        : {auto 0 fx : HasFixnums enc.val} -> Reg enc -> Reg enc -> Instr enc
  ||| The value of a `Fix`, as a `W64`.
  Untag      : {auto 0 fx : HasFixnums enc.val} -> Reg enc -> Reg enc -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`, or a branch to the label if the value
  ||| is outside the fixnum range. The label is a successor of the block at
  ||| this instruction, as for `ArithOv`.
  TagOv      : {auto 0 fx : HasFixnums enc.val} -> Reg enc -> Reg enc -> BlockLabel -> Instr enc
  ||| A `Val` as the type given, a `Fix` or a `PtrTo k`, which is the
  ||| destination's. No code: the producer guarantees it, after an `IsFixnum`
  ||| or a `Switch` on a header, or from static typing. The only way from a
  ||| `Val` to a fixnum or a pointer.
  Narrow     : Ty enc -> Reg enc -> Reg enc -> Instr enc
  ||| A `Fix` or a `PtrTo k` as a `Val`. No code.
  Widen      : Reg enc -> Reg enc -> Instr enc
  ||| A `PtrTo k` as a `W64`. No code. Only the functions of the module that
  ||| implements the runtime's memory interface make one (the term's
  ||| capability index): everywhere else no word can be derived from a
  ||| pointer, which is what lets the rooting stubs cover every pointer
  ||| there is.
  AddrToWord : Reg enc -> Reg enc -> Instr enc
  ||| A `W64` as a `PtrTo k`. No code. Restricted as `AddrToWord` is.
  WordToAddr : Kind -> Reg enc -> Reg enc -> Instr enc
  ||| The header word of the object a `PtrTo k` points to, as a `W64`. For a
  ||| `CONT`, which has no header, it is the layout word.
  LoadHeader : Reg enc -> Reg enc -> Instr enc
  ||| A part of the header of the object a `PtrTo k` points to, as a `W64`:
  ||| the constructor id of a `CON`, for instance. The pointer's kind is the
  ||| part's kind, which the instruction keeps, so that a pass reads it here
  ||| instead of rebuilding it from the part.
  LoadPart   : {k : Kind} -> HeaderPart k -> Reg enc -> Reg enc -> Instr enc
  ||| A whole object in one step: the destination, a `PtrTo k` of the
  ||| header's kind, becomes a new object with this header and these initial
  ||| fields. Since one instruction makes the whole object, no collection can
  ||| start between its allocation and its initialisation. The header is
  ||| known when the program is compiled, and so is its kind, which the
  ||| instruction keeps; there is no `Header enc CONT`.
  |||
  ||| It renders as an inline bump of the allocation pointer, with a slow
  ||| path that may collect. `live` is every register live across the
  ||| instruction, from which the rendering builds the slow path's stub: the
  ||| stub stores the GC-visible members in `ROOTS` and saves the raw ones,
  ||| since the slow path clobbers every register that is not pinned. Live
  ||| across includes the field registers, because the fields are written
  ||| after the slow path's collection. The rendering may rematerialise a
  ||| static's address instead of saving it.
  AllocObj   : {k : Kind} -> Reg enc -> Header enc k -> (fields : List (Operand enc)) ->
               (live : List (Reg enc)) -> Instr enc
  ||| A whole object whose size is known only at run time: the destination, a
  ||| `PtrTo k`, becomes a new object of the part's kind, whose size part is
  ||| `count`, a `W64`: an `ARRAY`'s elements, a `STRING`'s or a `BUFFER`'s
  ||| bytes. Every word the collector scans is set to `fill`, a `Val`, which a
  ||| kind that scans its fields needs and the others do not take; their bytes
  ||| are left as they are. As with `AllocObj`, one instruction makes the
  ||| whole object, so no collection can start before it is initialised.
  ||| `live` is every register live across it, the count and the fill
  ||| included, since both are read after the slow path's collection.
  |||
  ||| A count that does not fit the part's bits ends the program, as `Crash`
  ||| does. The rendering checks it, so no count can make an object smaller
  ||| than its header claims, a negative `Int` read as a word included.
  AllocSized : {k : Kind} -> Reg enc -> HeaderPart k -> (count : Reg enc) ->
               (fill : Maybe (Operand enc)) -> (live : List (Reg enc)) -> Instr enc
  ||| A machine call to a `Direct` function: one of the program's, or a
  ||| routine of the runtime. The registers receive the callee's results, in
  ||| order, where its `results` declares any. `mayCollect` says whether the callee may
  ||| start a collection. It is a fact about the callee, never read from a
  ||| type. The runtime's primitives never collect: when the nursery is full
  ||| they take a fresh window, and the next allocation slow path of
  ||| generated code collects. `live` is every register live across the
  ||| call, its results excluded. The rendering saves `live` around every
  ||| direct call, since a direct call clobbers every register that is not
  ||| pinned: across one that may collect, the GC-visible members in `ROOTS`,
  ||| where the collector updates them, and the rest on the stack; across one
  ||| that cannot, all of them on the stack, since nothing moves.
  DirectCall : Name -> List (Operand enc) -> (results : List (Reg enc)) -> (mayCollect : Bool) ->
               (live : List (Reg enc)) -> Instr enc
  ||| An intrinsic: a fixed instruction sequence, never a call.
  Intrinsic  : IntrinsicName -> Maybe (Reg enc) -> List (Operand enc) -> Instr enc
  ||| Copy a register to another of the same type: a jump's arguments into
  ||| its block's parameters.
  Move       : Reg enc -> Reg enc -> Instr enc
  ||| The source location of what follows, for dumps and, later, debugging
  ||| information.
  Loc        : FC -> Instr enc
  ||| A comment, for dumps.
  Comment    : String -> Instr enc

||| A short name for messages.
public export
instrName : Instr enc -> String
instrName (Const _ _) = "Const"
instrName (FConst _ _) = "FConst"
instrName (CodeAddr _ _) = "CodeAddr"
instrName (StaticAddr _ _) = "StaticAddr"
instrName (AreaAddr _ _) = "AreaAddr"
instrName (Arith op _ _ _) = show op
instrName (Unary Negate _ _) = "Negate"
instrName (Unary Complement _ _) = "Complement"
instrName (ArithOv op _ _ _ _) = show op ++ "Ov"
instrName (Ext _ _ _ _) = "Ext"
instrName (FArith op _ _ _) = show op
instrName (FNeg _ _) = "FNeg"
instrName (FCmp _ _ _ _) = "FCmp"
instrName (Convert _ _ _) = "Convert"
instrName (Cmp _ _ _ _) = "Cmp"
instrName (Load _ _ _) = "Load"
instrName (Store _ _ _) = "Store"
instrName (LoadN _ _ _ _) = "LoadN"
instrName (StoreN _ _ _) = "StoreN"
instrName (Tag _ _) = "Tag"
instrName (Untag _ _) = "Untag"
instrName (TagOv _ _ _) = "TagOv"
instrName (Narrow _ _ _) = "Narrow"
instrName (Widen _ _) = "Widen"
instrName (AddrToWord _ _) = "AddrToWord"
instrName (WordToAddr _ _ _) = "WordToAddr"
instrName (LoadHeader _ _) = "LoadHeader"
instrName (LoadPart p _ _) = "LoadPart " ++ show p
instrName (AllocObj _ _ _ _) = "AllocObj"
instrName (AllocSized _ _ _ _ _) = "AllocSized"
instrName (DirectCall f _ _ _ _) = "DirectCall " ++ show f
instrName (Intrinsic n _ _) = show n
instrName (Move _ _) = "Move"
instrName (Loc _) = "Loc"
instrName (Comment _) = "Comment"

------------------------------------------------------------------------------
-- Terminators

||| The whole of what the IR says about a continuation: where to resume, and
||| what is live there. The resume block's parameters are exactly `live`
||| followed by the result register. How the live values survive the call is
||| the rendering's business: under the heap lowering they become the fields
||| of a `CONT`, under the stack lowering slots of a frame.
public export
record Cont (enc : Enc) where
  constructor MkCont
  resume : BlockLabel
  live : List (Reg enc)

||| How a block ends; every block ends in exactly one terminator. Which ones a
||| function may use depends on its convention (`CallingConvention`).
public export
data BlockTerminator : Enc -> Type where
  ||| Continue at the block.
  Jump        : BlockLabel -> BlockTerminator enc
  ||| Branch on whether every one of the `Val`s is a fixnum, that is, on their
  ||| fixnum tags; the yes branch may narrow them to `Fix`es. The renderings
  ||| test the tags of several at once.
  IsFixnum    : {auto 0 fx : HasFixnums enc.val} -> List (Reg enc) -> (ifYes, ifNo : BlockLabel) -> BlockTerminator enc
  ||| Compare and branch, with the operand types of `Cmp`. Renderings fuse
  ||| the comparison and the branch.
  Branch      : Rel -> Operand enc -> Operand enc -> (ifTrue, ifFalse : BlockLabel) -> BlockTerminator enc
  ||| Branch on an integer to the block of the matching case, or else to the
  ||| default. The scrutinee is a `W64`, such as a constructor id from
  ||| `LoadPart`, or a `Fix`, whose cases are fixnums, as integers; the
  ||| rendering compares the words. The cases are distinct.
  Switch      : Reg enc -> List (Int64, BlockLabel) -> (dflt : BlockLabel) -> BlockTerminator enc
  ||| A non-tail call, CPS only: run the function, then continue at the
  ||| continuation's resume block, with its live registers and the result.
  Call        : Name -> List (Operand enc) -> Cont enc -> BlockTerminator enc
  ||| A tail call, CPS only: a transfer under the current continuation.
  TailCall    : Name -> List (Operand enc) -> BlockTerminator enc
  ||| A non-tail application of a closure to one argument, both `Val`s, CPS
  ||| only. It renders as a call to the runtime's apply routine.
  Apply       : (fn, arg : Reg enc) -> Cont enc -> BlockTerminator enc
  ||| A tail application, CPS only.
  TailApply   : (fn, arg : Reg enc) -> BlockTerminator enc
  ||| Deliver a `Val` to the current continuation, CPS only.
  Return      : Operand enc -> BlockTerminator enc
  ||| Jump to a code address held in a `W64`, with arguments, under the
  ||| current continuation. Allowed in both conventions; a `Direct`
  ||| function uses it only inside the runtime's `enterIdris` wrapper, the
  ||| one way from the runtime into Idris code.
  Enter       : Reg enc -> List (Operand enc) -> BlockTerminator enc
  ||| A machine return, `Direct` only, with the function's results, which
  ||| match its `results` in number and type.
  Ret         : List (Operand enc) -> BlockTerminator enc
  ||| Write the message to standard error and exit with status 1. There is
  ||| no unwinding.
  Crash       : String -> BlockTerminator enc
  ||| Exit with the abort status instead, for a construct the backend does
  ||| not lower yet: how an incomplete backend still links.
  Unsupported : String -> BlockTerminator enc

public export
termName : BlockTerminator enc -> String
termName (Jump _) = "Jump"
termName (IsFixnum _ _ _) = "IsFixnum"
termName (Branch _ _ _ _ _) = "Branch"
termName (Switch _ _ _) = "Switch"
termName (Call f _ _) = "Call " ++ show f
termName (TailCall f _) = "TailCall " ++ show f
termName (Apply _ _ _) = "Apply"
termName (TailApply _ _) = "TailApply"
termName (Return _) = "Return"
termName (Enter _ _) = "Enter"
termName (Ret _) = "Ret"
termName (Crash _) = "Crash"
termName (Unsupported _) = "Unsupported"

public export
termCont : BlockTerminator enc -> Maybe (Cont enc)
termCont (Call _ _ c) = Just c
termCont (Apply _ _ c) = Just c
termCont _ = Nothing

------------------------------------------------------------------------------
-- Functions, blocks, programs

||| A function's calling convention, as the term's (`Compiler.Native.TermIR.Conv`)
||| makes it.
public export
data CallingConvention
  = ||| Compiled Idris code, and the runtime routines that transfer control
    ||| into Idris code. A CPS function never executes a machine return:
    ||| control leaves it only by jumps. `Return`, `Call`, `TailCall`, `Apply`
    ||| and `TailApply` are allowed only here, and a `Call` or `TailCall`
    ||| targets a CPS function. A CPS function reaches `Direct` code only by
    ||| `DirectCall`.
    CPS
  | ||| Conventional machine call and return: the collector, the allocation
    ||| slow path, primitives. Only a Direct function ends in `Ret`, and only
    ||| a Direct function is the target of a `DirectCall`. It reaches CPS code
    ||| only by `Enter`, inside the runtime's `enterIdris` wrapper. The
    ||| collector must be Direct: as CPS code it would allocate continuations
    ||| in the space it is collecting.
    Direct

public export
Eq CallingConvention where
  CPS == CPS = True
  Direct == Direct = True
  _ == _ = False

public export
Show CallingConvention where
  show CPS = "CPS"
  show Direct = "Direct"

||| A basic block. Only a resume block has parameters: its continuation's
||| `live` list followed by the result register. They declare what the block
||| receives; they do not define registers. Every other block reads the
||| registers set before it.
public export
record Block (enc : Enc) where
  constructor MkBlock
  label : BlockLabel
  params : List (Reg enc)
  body : List (Instr enc)
  term : BlockTerminator enc

||| A function: its convention, its parameters in argument order, the types
||| of its results, its entry block, and its blocks. `fc` is its source
||| location, for dumps. A `Direct` function returns its results by `Ret`,
||| passed as arguments are (`Compiler.Native.Target.place`); a CPS function
||| has none, and delivers one `Val` to its continuation by `Return`.
public export
record Function (enc : Enc) where
  constructor MkFunction
  name : Name
  conv : CallingConvention
  params : List (Reg enc)
  results : List (Ty enc)
  entry : BlockLabel
  blocks : List (Block enc)
  fc : FC

||| A word of a static object.
public export
data StaticField
  = ||| A raw word or an immediate value.
    SWord Int64
  | ||| The address of another static. Reserved for constant data built from
    ||| statics; nothing makes one yet.
    SRef Name
  | ||| The entry address of a function of the program, such as `HALT`'s code
    ||| or a static closure's: the only absolute addresses in an image, and
    ||| so the only words a position-independent image would relocate.
    SCode Name

||| A static object: an object the compiler creates in the image's read-only
||| data, laid out exactly as a heap object of its kind, and never
||| allocated, moved, freed or written. `fields` are the words after its
||| header. A static never points into a collected space, which lets the
||| collector recognise statics by address alone and leave them untouched.
public export
record Static (enc : Enc) where
  constructor MkStatic
  sym : Name
  kind : Kind
  header : Header enc kind
  fields : List StaticField


||| A whole program: its target, functions, statics, entry function and
||| constructor numbering.
public export
record Program (enc : Enc) where
  constructor MkProgram
  target : Target
  functions : List (Function enc)
  statics : List (Static enc)
  entry : Name
  conIds : ConIds
