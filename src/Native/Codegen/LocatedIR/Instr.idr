||| The instructions of the located IR (`Instr`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Instr

import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Mem
import Native.Codegen.LocatedIR.Opnd
import Native.Codegen.LocatedIR.Reg

import Core.FC
import Core.Name
import Native.Area
import Native.Codegen.IRCommon.Intrinsic as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.Header as HeapObj
import Native.HeapObj.Kind as HeapObj
import Native.HeapObj.ValEnc

%default total

||| An instruction. Each defines at most one register, its destination,
||| which comes first. The types stated here are the term's
||| (`Native.Codegen.TermIR.Program`), which the conversion keeps.
public export
data Instr : HeapObj.Enc -> Type where
  ||| A constant, into a `W64`, a `Val` or a `Fix`. Into a `W64` it is the
  ||| word itself. Into a `Val` or a `Fix` it is the integer, and the
  ||| rendering turns it into the value encoding's word (`valWord` in
  ||| `HeapObj.ValEnc`), so that the IR is the same under every value
  ||| encoding; as a `Val`, 0 is also the erased value. No constant is a
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
  Arith      : IRCommon.Op.ArithOp -> Reg enc -> Opnd enc -> Opnd enc -> Instr enc
  ||| Negation or complement of a `W64`.
  Unary      : IRCommon.Op.UnOp -> Reg enc -> Reg enc -> Instr enc
  ||| `Add`, `Sub` or `Mul`, with the operand types of `Arith`, then a branch
  ||| to the label if the result does not fit: in 64 signed bits for `W64`s,
  ||| in the fixnum range for `Fix`es, which is the fixnum fast path. The
  ||| label is a successor of the block at this instruction, not at the
  ||| block's end.
  ArithOv    : IRCommon.Op.ArithOp -> Reg enc -> Opnd enc -> Opnd enc -> Label -> Instr enc
  ||| Narrow a `W64` to the width, then sign- or zero-extend it back to 64
  ||| bits.
  Ext        : IRCommon.Op.SubWord -> (signed : Bool) -> Reg enc -> Reg enc -> Instr enc
  ||| Double arithmetic on `F64`s.
  FArith     : IRCommon.Op.FOp -> Reg enc -> Reg enc -> Reg enc -> Instr enc
  ||| Double negation.
  FNeg       : Reg enc -> Reg enc -> Instr enc
  ||| Compare two `F64`s; the destination, a `W64`, is 1 or 0.
  FCmp       : IRCommon.Op.Rel -> Reg enc -> Reg enc -> Reg enc -> Instr enc
  ||| Convert between a `W64` and an `F64`.
  Convert    : IRCommon.Op.ConvOp -> Reg enc -> Reg enc -> Instr enc
  ||| Compare two integers; the destination, a `W64`, is 1 or 0. The operands
  ||| are both `W64`s or both `Fix`es, compared as `Rel` says; a comparison
  ||| never makes a value.
  Cmp        : IRCommon.Op.Rel -> Reg enc -> Opnd enc -> Opnd enc -> Instr enc
  ||| Load a word of the given type.
  Load       : IRCommon.Ty enc -> Reg enc -> Mem enc -> Instr enc
  ||| Store a register of the given type.
  Store      : IRCommon.Ty enc -> Mem enc -> Reg enc -> Instr enc
  ||| Load 8, 16 or 32 bits into a `W64`, zero- or sign-extended: the bytes
  ||| of strings and buffers, the limbs of bignums.
  LoadN      : IRCommon.Op.SubWord -> (signed : Bool) -> Reg enc -> Mem enc -> Instr enc
  ||| Store the low 8, 16 or 32 bits of a `W64`.
  StoreN     : IRCommon.Op.SubWord -> Mem enc -> Reg enc -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`. The producer guarantees that the
  ||| value is in the fixnum range.
  Tag        : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Reg enc -> Reg enc -> Instr enc
  ||| The value of a `Fix`, as a `W64`.
  Untag      : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Reg enc -> Reg enc -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`, or a branch to the label if the value
  ||| is outside the fixnum range. The label is a successor of the block at
  ||| this instruction, as for `ArithOv`.
  TagOv      : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Reg enc -> Reg enc -> Label -> Instr enc
  ||| A `Val` as the type given, a `Fix` or a `PtrTo k`, which is the
  ||| destination's. No code: the producer guarantees it, after an `IfFixnums`
  ||| or a `Switch` on a header, or from static typing. The only way from a
  ||| `Val` to a fixnum or a pointer.
  Narrow     : IRCommon.Ty enc -> Reg enc -> Reg enc -> Instr enc
  ||| A `Fix` or a `PtrTo k` as a `Val`. No code.
  Widen      : Reg enc -> Reg enc -> Instr enc
  ||| A `PtrTo k` as a `W64`. No code. Only the functions of the module that
  ||| implements the runtime's memory interface make one (the term's
  ||| capability index): everywhere else no word can be derived from a
  ||| pointer, which is what lets the rooting stubs cover every pointer
  ||| there is.
  AddrToWord : Reg enc -> Reg enc -> Instr enc
  ||| A `W64` as a `PtrTo k`. No code. Restricted as `AddrToWord` is.
  WordToAddr : HeapObj.Kind -> Reg enc -> Reg enc -> Instr enc
  ||| The header word of the object a `PtrTo k` points to, as a `W64`. For a
  ||| `CONT`, which has no header, it is the layout word.
  LoadHeader : Reg enc -> Reg enc -> Instr enc
  ||| A part of the header of the object a `PtrTo k` points to, as a `W64`:
  ||| the constructor id of a `CON`, for instance. The pointer's kind is the
  ||| part's kind, which the instruction keeps, so that a pass reads it here
  ||| instead of rebuilding it from the part.
  LoadPart   : {0 k : HeapObj.Kind} -> HeapObj.Header.HeaderPart k -> Reg enc -> Reg enc -> Instr enc
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
  AllocObj   : {k : HeapObj.Kind} -> Reg enc -> HeapObj.Header enc k -> (fields : List (Opnd enc)) ->
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
  AllocSized : {k : HeapObj.Kind} -> Reg enc -> HeapObj.Header.HeaderPart k -> (count : Reg enc) ->
               (fill : Maybe (Opnd enc)) -> (live : List (Reg enc)) -> Instr enc
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
  DirectCall : Name -> List (Opnd enc) -> (results : List (Reg enc)) -> (mayCollect : Bool) ->
               (live : List (Reg enc)) -> Instr enc
  ||| An intrinsic: a fixed instruction sequence, never a call, giving its
  ||| results from its operands.
  Intrinsic  : Intrinsic -> (results : List (Reg enc)) -> List (Opnd enc) -> Instr enc
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
instrName (Unary IRCommon.Op.Negate _ _) = "Negate"
instrName (Unary IRCommon.Op.Complement _ _) = "Complement"
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
