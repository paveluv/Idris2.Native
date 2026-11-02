||| The instructions of the located IR (`Instr`).
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Instr

import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Mem
import Native.Codegen.LocatedIR.Opnd

import Core.FC
import Core.Name
import Native.Area
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types
import Native.Width

%default total

||| An instruction, what a step of a block that realises an instruction of
||| the term does (`Native.Codegen.LocatedIR.Step`). Most define one
||| register, their destination, which comes first; `Mul128` and `Div128`
||| define two, and `DirectCall` the callee's results. The types of its
||| locations and operands are its index's, the term's
||| (`Native.Codegen.TermIR.Program`), which the conversion keeps.
public export
data Instr : Types.Enc -> Type where
  ||| A double constant, into an `F64`.
  FConst     : Location enc IRCommon.Ty.F64 -> Double -> Instr enc
  ||| The entry address of a function of this program, into a `CodeAddr`: a
  ||| closure's code pointer.
  CodeOf     : Location enc IRCommon.Ty.CodeAddr -> Name -> Instr enc
  ||| The address of a per-thread area, into a `ByteAddr`.
  AreaAddr   : Location enc IRCommon.Ty.ByteAddr -> Area -> Instr enc
  ||| A byte address moved by a count of bytes, into a `ByteAddr`.
  Offset     : Location enc IRCommon.Ty.ByteAddr -> Opnd enc IRCommon.Ty.ByteAddr ->
    Opnd enc IRCommon.Ty.W64 ->
               Instr enc
  ||| Integer arithmetic: the operands and the result are all `W64`s, or all
  ||| `Fix`es. On `Fix`es it is the operation on the fixnums' values, which
  ||| the producer guarantees is in the fixnum range, and the rendering
  ||| computes it on the words, without untagging where the value encoding has
  ||| an identity for it. There is no arithmetic on `Val`s: a `Val` is narrowed
  ||| to a `Fix` first.
  Arith      : {0 t : IRCommon.Ty enc} -> IRCommon.Op.ArithOp -> Location enc t -> Opnd enc t ->
    Opnd enc t ->
               Instr enc
  ||| The 128-bit product of two words, into its high word and its low word.
  Mul128     : (high, low : Location enc IRCommon.Ty.W64) -> Opnd enc IRCommon.Ty.W64 ->
    Opnd enc IRCommon.Ty.W64 ->
               Instr enc
  ||| The quotient and the remainder of the 128-bit number of the high and
  ||| the low word by the divisor.
  Div128     : (quotient, remainder : Location enc IRCommon.Ty.W64) ->
               (high, low, divisor : Opnd enc IRCommon.Ty.W64) -> Instr enc
  ||| Negation or complement of a `W64`.
  Unary      : IRCommon.Op.UnOp -> Location enc IRCommon.Ty.W64 -> Location enc IRCommon.Ty.W64 ->
    Instr enc
  ||| `Add`, `Sub` or `Mul`, with the operand types of `Arith`, then a branch
  ||| to the label if the result does not fit: in 64 signed bits for `W64`s,
  ||| in the fixnum range for `Fix`es, which is the fixnum fast path. The
  ||| label is a successor of the block at this instruction, not at the
  ||| block's end.
  ArithOv    : {0 t : IRCommon.Ty enc} -> IRCommon.Op.ArithOp -> Location enc t -> Opnd enc t ->
    Opnd enc t ->
               Label -> Instr enc
  ||| Narrow a `W64` to the width, then sign- or zero-extend it back to 64
  ||| bits.
  Ext        : Width.SubWord -> (signed : Bool) -> Location enc IRCommon.Ty.W64 ->
    Location enc IRCommon.Ty.W64 ->
               Instr enc
  ||| Double arithmetic on `F64`s.
  FArith     : IRCommon.Op.FOp -> Location enc IRCommon.Ty.F64 -> Location enc IRCommon.Ty.F64 ->
    Location enc IRCommon.Ty.F64 ->
               Instr enc
  ||| Double negation.
  FNeg       : Location enc IRCommon.Ty.F64 -> Location enc IRCommon.Ty.F64 -> Instr enc
  FSqrt      : Location enc IRCommon.Ty.F64 -> Location enc IRCommon.Ty.F64 -> Instr enc
  ||| Compare two `F64`s; the destination, a `W64`, is 1 or 0.
  FCmp       : IRCommon.Op.Rel -> Location enc IRCommon.Ty.W64 -> Location enc IRCommon.Ty.F64 ->
    Location enc IRCommon.Ty.F64 ->
               Instr enc
  ||| Convert between a `W64` and an `F64`.
  Convert    : (op : IRCommon.Op.ConvOp) -> Location enc (IRCommon.Op.convTo op) ->
               Location enc (IRCommon.Op.convFrom op) -> Instr enc
  ||| Compare two integers; the destination, a `W64`, is 1 or 0. The operands
  ||| are both `W64`s or both `Fix`es, compared as `Rel` says; a comparison
  ||| never makes a value.
  Cmp        : {0 t : IRCommon.Ty enc} -> IRCommon.Op.Rel -> Location enc IRCommon.Ty.W64 ->
    Opnd enc t -> Opnd enc t -> Instr enc
  ||| Load a word of the given type.
  Load       : (t : IRCommon.Ty enc) -> Location enc t -> Mem enc -> Instr enc
  ||| Store a register of the given type.
  Store      : (t : IRCommon.Ty enc) -> Mem enc -> Location enc t -> Instr enc
  ||| Load 8, 16 or 32 bits into a `W64`, zero- or sign-extended: the bytes
  ||| of strings and buffers, the limbs of bignums.
  LoadN      : Width.SubWord -> (signed : Bool) -> Location enc IRCommon.Ty.W64 -> Mem enc ->
    Instr enc
  ||| Store the low 8, 16 or 32 bits of a `W64`.
  StoreN     : Width.SubWord -> Mem enc -> Location enc IRCommon.Ty.W64 -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`. The producer guarantees that the
  ||| value is in the fixnum range.
  Tag        : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
    Location enc (IRCommon.Ty.Fix {enc}) ->
               Location enc IRCommon.Ty.W64 -> Instr enc
  ||| The value of a `Fix`, as a `W64`.
  Untag      : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Location enc IRCommon.Ty.W64 ->
               Location enc (IRCommon.Ty.Fix {enc}) -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`, or a branch to the label if the value
  ||| is outside the fixnum range. The label is a successor of the block at
  ||| this instruction, as for `ArithOv`.
  TagOv      : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
    Location enc (IRCommon.Ty.Fix {enc}) ->
               Location enc IRCommon.Ty.W64 -> Label -> Instr enc
  ||| A `Val` as the type given, a `Fix` or a `PtrTo k`, which is the
  ||| destination's. No code: the producer guarantees it, after an `IfFixnums`
  ||| or a `Switch` on a header, or from static typing. The only way from a
  ||| `Val` to a fixnum or a pointer.
  Narrow     : (t : IRCommon.Ty enc) -> Location enc t -> Location enc IRCommon.Ty.Val -> Instr enc
  ||| A `Fix` or a `PtrTo k` as a `Val`. No code.
  Widen      : {0 t : IRCommon.Ty enc} -> Location enc IRCommon.Ty.Val -> Location enc t ->
    Instr enc
  ||| A `PtrTo k` as a `W64`. No code. Only the functions of the module that
  ||| implements the runtime's memory interface make one (the term's
  ||| capability index): everywhere else no word can be derived from a
  ||| pointer, which is what lets the rooting stubs cover every pointer
  ||| there is.
  AddrToWord : {0 k : Types.Kind} -> Location enc IRCommon.Ty.W64 ->
               Location enc (IRCommon.Ty.PtrTo k) -> Instr enc
  ||| A `W64` as a `PtrTo k`. No code. Restricted as `AddrToWord` is.
  WordToAddr : (k : Types.Kind) -> Location enc (IRCommon.Ty.PtrTo k) ->
               Location enc IRCommon.Ty.W64 ->
               Instr enc
  ||| A `Val` as a `W64`, and a `W64` as a `Val`. No code. Restricted as
  ||| `AddrToWord` is.
  ValToWord  : Location enc IRCommon.Ty.W64 -> Location enc IRCommon.Ty.Val -> Instr enc
  WordToVal  : Location enc IRCommon.Ty.Val -> Location enc IRCommon.Ty.W64 -> Instr enc
  ||| The header word of the object a `PtrTo k` points to, as a `W64`. For a
  ||| `CONT`, which has no header, it is the layout word.
  LoadHeader : {0 k : Types.Kind} -> Location enc IRCommon.Ty.W64 ->
               Location enc (IRCommon.Ty.PtrTo k) -> Instr enc
  ||| A part of the header of the object a `PtrTo k` points to, as a `W64`:
  ||| the constructor id of a `CON`, for instance. The pointer's kind is the
  ||| part's kind, which the instruction keeps, so that a pass reads it here
  ||| instead of rebuilding it from the part.
  LoadPart   : {0 k : Types.Kind} -> Types.Header.HeaderPart k -> Location enc IRCommon.Ty.W64 ->
               Location enc (IRCommon.Ty.PtrTo k) -> Instr enc
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
  AllocObj   : {k : Types.Kind} -> Location enc (IRCommon.Ty.PtrTo k) -> Types.Header enc k ->
               (fields : List (Opnd.Arg enc)) -> (live : List (Location.Place enc)) -> Instr enc
  ||| A whole object whose size is known only at run time: the destination, a
  ||| `PtrTo k`, becomes a new object of the part's kind, whose size part is
  ||| `count`, a `W64`: an `ARRAY`'s elements, a `STRING`'s or a `BYTES`'s
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
  AllocSized : {k : Types.Kind} -> Location enc (IRCommon.Ty.PtrTo k) ->
               Types.Header.HeaderPart k -> (count : Location enc IRCommon.Ty.W64) ->
               (fill : Maybe (Opnd enc IRCommon.Ty.Val)) -> (live : List (Location.Place enc)) ->
                 Instr enc
  ||| A machine call to a `Direct` function: one of the program's, or a
  ||| routine of the runtime. The registers receive the callee's results, in
  ||| order, where its `results` declares any. `mayCollect` says whether the callee may
  ||| start a collection. It is a fact about the callee, never read from a
  ||| type. The runtime's primitives never collect: when the nursery is full
  ||| they take a fresh window, and the next allocation slow path of
  ||| generated code collects. `live` is every register live across the
  ||| call, its results excluded. The callee's slots are in a frame of its
  ||| own, so the call keeps every slot of its caller's; across a call that
  ||| may collect, the rendering keeps the GC-visible members of `live` in
  ||| `ROOTS`, where the collector forwards them, and reloads them after.
  DirectCall : Name -> List (Opnd.Arg enc) -> (results : List (Location.Place enc)) ->
               (mayCollect : Bool) ->
               (live : List (Location.Place enc)) -> Instr enc
  ||| A pinned register's value, and setting it.
  GetPinned  : (p : IRCommon.Pinned) -> (result : Location enc (IRCommon.Pinned.ty p)) ->
               Instr enc
  SetPinned  : (p : IRCommon.Pinned) -> Opnd enc (IRCommon.Pinned.ty p) -> Instr enc
  ||| A system call: its number, then its arguments, giving its result, by
  ||| the platform's convention; never a call of a function.
  SystemCall : (result : Location enc IRCommon.Ty.W64) -> List (Opnd enc IRCommon.Ty.W64) ->
               Instr enc
  ||| The source location of what follows, for dumps and, later, debugging
  ||| information.
  Loc        : FC -> Instr enc
  ||| A comment, for dumps.
  Comment    : String -> Instr enc

||| A short name for messages.
public export
instrName : Instr enc -> String
instrName (FConst _ _) = "FConst"
instrName (CodeOf _ _) = "CodeOf"
instrName (AreaAddr _ _) = "AreaAddr"
instrName (Offset _ _ _) = "Offset"
instrName (Arith op _ _ _) = show op
instrName (Unary IRCommon.Op.Negate _ _) = "Negate"
instrName (Unary IRCommon.Op.Complement _ _) = "Complement"
instrName (ArithOv op _ _ _ _) = show op ++ "Ov"
instrName (Ext _ _ _ _) = "Ext"
instrName (FArith op _ _ _) = show op
instrName (FNeg _ _) = "FNeg"
instrName (FSqrt _ _) = "FSqrt"
instrName (Mul128 _ _ _ _) = "Mul128"
instrName (Div128 _ _ _ _ _) = "Div128"
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
instrName (ValToWord _ _) = "ValToWord"
instrName (WordToVal _ _) = "WordToVal"
instrName (LoadHeader _ _) = "LoadHeader"
instrName (LoadPart p _ _) = "LoadPart " ++ show p
instrName (AllocObj _ _ _ _) = "AllocObj"
instrName (AllocSized _ _ _ _ _) = "AllocSized"
instrName (DirectCall f _ _ _ _) = "DirectCall " ++ show f
instrName (GetPinned r _) = "get" ++ show r
instrName (SetPinned r _) = "set" ++ show r
instrName (SystemCall _ _) = "syscall"
instrName (Loc _) = "Loc"
instrName (Comment _) = "Comment"

||| A memory operand's registers, its base before its index.
memRegs : Mem enc -> List (Location.Place enc)
memRegs m = Mem.place m.base :: maybe [] (\r => [Location.At r]) m.index

||| What an instruction reads, its register operands, in the order of its
||| fields, a memory operand's base before its index: not the registers its
||| `live` list keeps.
export
operands : Instr enc -> List (Location.Place enc)
operands i = case i of
  Offset _ x y => Opnd.opRegs x ++ Opnd.opRegs y
  Arith _ _ x y => Opnd.opRegs x ++ Opnd.opRegs y
  Mul128 _ _ x y => Opnd.opRegs x ++ Opnd.opRegs y
  Div128 _ _ h l x => Opnd.opRegs h ++ Opnd.opRegs l ++ Opnd.opRegs x
  Unary _ _ x => [Location.At x]
  ArithOv _ _ x y _ => Opnd.opRegs x ++ Opnd.opRegs y
  Ext _ _ _ x => [Location.At x]
  FArith _ _ x y => [Location.At x, Location.At y]
  FNeg _ x => [Location.At x]
  FSqrt _ x => [Location.At x]
  FCmp _ _ x y => [Location.At x, Location.At y]
  Convert _ _ x => [Location.At x]
  Cmp _ _ x y => Opnd.opRegs x ++ Opnd.opRegs y
  Load _ _ m => memRegs m
  Store _ m x => Location.At x :: memRegs m
  LoadN _ _ _ m => memRegs m
  StoreN _ m x => Location.At x :: memRegs m
  Tag _ x => [Location.At x]
  Untag _ x => [Location.At x]
  TagOv _ x _ => [Location.At x]
  Narrow _ _ x => [Location.At x]
  Widen _ x => [Location.At x]
  AddrToWord _ x => [Location.At x]
  WordToAddr _ _ x => [Location.At x]
  ValToWord _ x => [Location.At x]
  WordToVal _ x => [Location.At x]
  LoadHeader _ x => [Location.At x]
  LoadPart _ _ x => [Location.At x]
  AllocObj _ _ fs _ => Opnd.opsRegs fs []
  AllocSized _ _ count fill _ => Location.At count :: maybe [] Opnd.opRegs fill
  DirectCall _ args _ _ _ => Opnd.opsRegs args []
  SetPinned _ x => Opnd.opRegs x
  SystemCall _ args => concatMap Opnd.opRegs args
  _ => []

||| What an instruction writes, in the order of its fields.
export
results : Instr enc -> List (Location.Place enc)
results i = case i of
  FConst d _ => [Location.At d]
  CodeOf d _ => [Location.At d]
  AreaAddr d _ => [Location.At d]
  Offset d _ _ => [Location.At d]
  Arith _ d _ _ => [Location.At d]
  Mul128 h l _ _ => [Location.At h, Location.At l]
  Div128 q r _ _ _ => [Location.At q, Location.At r]
  Unary _ d _ => [Location.At d]
  ArithOv _ d _ _ _ => [Location.At d]
  Ext _ _ d _ => [Location.At d]
  FArith _ d _ _ => [Location.At d]
  FNeg d _ => [Location.At d]
  FSqrt d _ => [Location.At d]
  FCmp _ d _ _ => [Location.At d]
  Convert _ d _ => [Location.At d]
  Cmp _ d _ _ => [Location.At d]
  Load _ d _ => [Location.At d]
  LoadN _ _ d _ => [Location.At d]
  Tag d _ => [Location.At d]
  Untag d _ => [Location.At d]
  TagOv d _ _ => [Location.At d]
  Narrow _ d _ => [Location.At d]
  Widen d _ => [Location.At d]
  AddrToWord d _ => [Location.At d]
  WordToAddr _ d _ => [Location.At d]
  ValToWord d _ => [Location.At d]
  WordToVal d _ => [Location.At d]
  LoadHeader d _ => [Location.At d]
  LoadPart _ d _ => [Location.At d]
  AllocObj d _ _ _ => [Location.At d]
  AllocSized d _ _ _ _ => [Location.At d]
  DirectCall _ _ ds _ _ => ds
  GetPinned _ d => [Location.At d]
  SystemCall d _ => [Location.At d]
  _ => []

||| The `live` list of an instruction that has one, an allocation or a
||| direct call: every register live across it.
export
listed : Instr enc -> Maybe (List (Location.Place enc))
listed (AllocObj _ _ _ live) = Just live
listed (AllocSized _ _ _ _ live) = Just live
listed (DirectCall _ _ _ _ live) = Just live
listed _ = Nothing

||| The `live` list of an instruction where a collection can start, an
||| allocation or a direct call that may collect: every register the
||| collector keeps, the GC-visible ones forwarded.
export
collecting : Instr enc -> Maybe (List (Location.Place enc))
collecting (DirectCall _ _ _ False _) = Nothing
collecting i = listed i

||| Whether objects of the kind are allocated by a call to the runtime's
||| `idris_alloc_mutable`, never by the inline bump: the kinds whose objects
||| hold values the collector follows and are written after they are made,
||| so that a collector with a nursery can keep them out of it, and then a
||| write into an old object never makes it point into the nursery. A raw
||| object (`BYTES`) may be written too, but holds no pointer, so the bump
||| serves it.
export
isMutable : Types.Kind -> Bool
isMutable Types.Kind.IOREF = True
isMutable Types.Kind.ARRAY = True
isMutable Types.Kind.STRUCT = True
isMutable _ = False

||| Whether the instruction is an allocation, which initialises its object
||| from its operands after the collection it may start, where any other
||| operation reads them first.
export
isAllocation : Instr enc -> Bool
isAllocation (AllocObj _ _ _ _) = True
isAllocation (AllocSized _ _ _ _ _) = True
isAllocation _ = False

||| The registers the instruction names, its destinations, its operands'
||| and its memory operands', and those it keeps live: each as often as it
||| names it, in no order to rely on.
export
instrRegs : Instr enc -> List (Location.Place enc)
instrRegs i = results i ++ operands i ++ maybe [] id (listed i)

||| The instruction with its register operands replaced by the step, in the
||| order `operands` lists them.
export
traverseOperands : Location.Step s enc -> s -> Instr enc -> (s, Instr enc)
traverseOperands f st i = case i of
  Offset d x y => let (s1, x') = opnd st x; (s2, y') = opnd s1 y in (s2, Offset d x' y')
  Arith o d x y => let (s1, x') = opnd st x; (s2, y') = opnd s1 y in (s2, Arith o d x' y')
  Mul128 h l x y => let (s1, x') = opnd st x; (s2, y') = opnd s1 y in (s2, Mul128 h l x' y')
  Div128 q r h l x =>
    let (s1, h') = opnd st h; (s2, l') = opnd s1 l; (s3, x') = opnd s2 x
    in (s3, Div128 q r h' l' x')
  Unary o d x => let (s1, x') = f st x in (s1, Unary o d x')
  ArithOv o d x y l => let (s1, x') = opnd st x; (s2, y') = opnd s1 y in (s2, ArithOv o d x' y' l)
  Ext w sg d x => let (s1, x') = f st x in (s1, Ext w sg d x')
  FArith o d x y => let (s1, x') = f st x; (s2, y') = f s1 y in (s2, FArith o d x' y')
  FNeg d x => let (s1, x') = f st x in (s1, FNeg d x')
  FSqrt d x => let (s1, x') = f st x in (s1, FSqrt d x')
  FCmp r d x y => let (s1, x') = f st x; (s2, y') = f s1 y in (s2, FCmp r d x' y')
  Convert c d x => let (s1, x') = f st x in (s1, Convert c d x')
  Cmp r d x y => let (s1, x') = opnd st x; (s2, y') = opnd s1 y in (s2, Cmp r d x' y')
  Load t d m => let (s1, m') = mem st m in (s1, Load t d m')
  Store t m x => let (s1, x') = f st x; (s2, m') = mem s1 m in (s2, Store t m' x')
  LoadN w sg d m => let (s1, m') = mem st m in (s1, LoadN w sg d m')
  StoreN w m x => let (s1, x') = f st x; (s2, m') = mem s1 m in (s2, StoreN w m' x')
  Tag d x => let (s1, x') = f st x in (s1, Tag d x')
  Untag d x => let (s1, x') = f st x in (s1, Untag d x')
  TagOv d x l => let (s1, x') = f st x in (s1, TagOv d x' l)
  Narrow t d x => let (s1, x') = f st x in (s1, Narrow t d x')
  Widen d x => let (s1, x') = f st x in (s1, Widen d x')
  AddrToWord d x => let (s1, x') = f st x in (s1, AddrToWord d x')
  WordToAddr k d x => let (s1, x') = f st x in (s1, WordToAddr k d x')
  ValToWord d x => let (s1, x') = f st x in (s1, ValToWord d x')
  WordToVal d x => let (s1, x') = f st x in (s1, WordToVal d x')
  LoadHeader d x => let (s1, x') = f st x in (s1, LoadHeader d x')
  LoadPart p d x => let (s1, x') = f st x in (s1, LoadPart p d x')
  AllocObj d h fs live => let (s1, fs') = Opnd.stepArgs f st fs in (s1, AllocObj d h fs' live)
  AllocSized d p count fill live =>
    let (s1, count') = f st count; (s2, fill') = maybeOpnd s1 fill
    in (s2, AllocSized d p count' fill' live)
  DirectCall n args ds m live => let (s1, args') =
                                       Opnd.stepArgs f st args in (s1, DirectCall n args' ds m live)
  SetPinned p x => let (s1, x') = opnd st x in (s1, SetPinned p x')
  SystemCall d args => let (s1, args') = opnds st args in (s1, SystemCall d args')
  _ => (st, i)
  where
    opnd : {0 t : IRCommon.Ty enc} -> s -> Opnd enc t -> (s, Opnd enc t)
    opnd = Opnd.stepOpnd f

    opnds : {0 t : IRCommon.Ty enc} -> s -> List (Opnd enc t) -> (s, List (Opnd enc t))
    opnds st' [] = (st', [])
    opnds st' (o :: os) = let (s1, o') = opnd st' o; (s2, os') = opnds s1 os in (s2, o' :: os')

    maybeOpnd : {0 t : IRCommon.Ty enc} -> s -> Maybe (Opnd enc t) -> (s, Maybe (Opnd enc t))
    maybeOpnd st' (Just o) = let (s1, o') = opnd st' o in (s1, Just o')
    maybeOpnd st' Nothing = (st', Nothing)

    maybeLoc : {0 t : IRCommon.Ty enc} -> s -> Maybe (Location enc t) ->
               (s, Maybe (Location enc t))
    maybeLoc st' (Just l) = let (s1, l') = f st' l in (s1, Just l')
    maybeLoc st' Nothing = (st', Nothing)

    mem : s -> Mem enc -> (s, Mem enc)
    mem st' m =
      let (s1, b') = Mem.stepBase f st' m.base; (s2, ix') = maybeLoc s1 m.index
      in (s2, { base := b', index := ix' } m)

||| The instruction with its results replaced by the step, in the order
||| `results` lists them.
export
traverseResults : Location.Step s enc -> s -> Instr enc -> (s, Instr enc)
traverseResults f st i = case i of
  FConst d c => let (s1, d') = f st d in (s1, FConst d' c)
  CodeOf d n => let (s1, d') = f st d in (s1, CodeOf d' n)
  AreaAddr d a => let (s1, d') = f st d in (s1, AreaAddr d' a)
  Offset d x y => let (s1, d') = f st d in (s1, Offset d' x y)
  Arith o d x y => let (s1, d') = f st d in (s1, Arith o d' x y)
  Mul128 h l x y => let (s1, h') = f st h; (s2, l') = f s1 l in (s2, Mul128 h' l' x y)
  Div128 q r h l x => let (s1, q') = f st q; (s2, r') = f s1 r in (s2, Div128 q' r' h l x)
  Unary o d x => let (s1, d') = f st d in (s1, Unary o d' x)
  ArithOv o d x y l => let (s1, d') = f st d in (s1, ArithOv o d' x y l)
  Ext w sg d x => let (s1, d') = f st d in (s1, Ext w sg d' x)
  FArith o d x y => let (s1, d') = f st d in (s1, FArith o d' x y)
  FNeg d x => let (s1, d') = f st d in (s1, FNeg d' x)
  FSqrt d x => let (s1, d') = f st d in (s1, FSqrt d' x)
  FCmp r d x y => let (s1, d') = f st d in (s1, FCmp r d' x y)
  Convert c d x => let (s1, d') = f st d in (s1, Convert c d' x)
  Cmp r d x y => let (s1, d') = f st d in (s1, Cmp r d' x y)
  Load t d m => let (s1, d') = f st d in (s1, Load t d' m)
  LoadN w sg d m => let (s1, d') = f st d in (s1, LoadN w sg d' m)
  Tag d x => let (s1, d') = f st d in (s1, Tag d' x)
  Untag d x => let (s1, d') = f st d in (s1, Untag d' x)
  TagOv d x l => let (s1, d') = f st d in (s1, TagOv d' x l)
  Narrow t d x => let (s1, d') = f st d in (s1, Narrow t d' x)
  Widen d x => let (s1, d') = f st d in (s1, Widen d' x)
  AddrToWord d x => let (s1, d') = f st d in (s1, AddrToWord d' x)
  WordToAddr k d x => let (s1, d') = f st d in (s1, WordToAddr k d' x)
  ValToWord d x => let (s1, d') = f st d in (s1, ValToWord d' x)
  WordToVal d x => let (s1, d') = f st d in (s1, WordToVal d' x)
  LoadHeader d x => let (s1, d') = f st d in (s1, LoadHeader d' x)
  LoadPart p d x => let (s1, d') = f st d in (s1, LoadPart p d' x)
  AllocObj d h fs live => let (s1, d') = f st d in (s1, AllocObj d' h fs live)
  AllocSized d p count fill live => let (s1, d') = f st d in (s1, AllocSized d' p count fill live)
  DirectCall n args ds m live =>
    let (s1, ds') = Location.stepPlaces f st ds in (s1, DirectCall n args ds' m live)
  GetPinned p d => let (s1, d') = f st d in (s1, GetPinned p d')
  SystemCall d args => let (s1, d') = f st d in (s1, SystemCall d' args)
  _ => (st, i)
