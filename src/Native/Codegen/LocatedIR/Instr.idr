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
import Data.List
import Data.Maybe
import Data.Zippable
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

||| An instruction. Most define one register, their destination, which
||| comes first; `Mul128` and `Div128` define two, and `DirectCall` the
||| callee's results. The types stated here are the term's
||| (`Native.Codegen.TermIR.Program`), which the conversion keeps.
public export
data Instr : Types.Enc -> Type where
  ||| A constant, into a `W64`, a `Val` or a `Fix`. Into a `W64` it is the
  ||| word itself. Into a `Val` or a `Fix` it is the integer, and the
  ||| rendering turns it into the value encoding's word (`valWord` in
  ||| `HeapObj.ValEnc`), so that the IR is the same under every value
  ||| encoding; as a `Val`, 0 is also the erased value. No constant is a
  ||| pointer.
  Const      : Location enc -> Int64 -> Instr enc
  ||| A double constant, into an `F64`.
  FConst     : Location enc -> Double -> Instr enc
  ||| The entry address of a function of this program, into a `CodeAddr`: a
  ||| closure's code pointer.
  CodeOf     : Location enc -> Name -> Instr enc
  ||| The address of a static object of this program, into a `Val`, or into a
  ||| `PtrTo k` of the static's kind.
  StaticAddr : Location enc -> Name -> Instr enc
  ||| The address of a per-thread area, into a `ByteAddr`.
  AreaAddr   : Location enc -> Area -> Instr enc
  ||| Integer arithmetic: the operands and the result are all `W64`s, or all
  ||| `Fix`es; or a byte address moved by a `W64`, an `Add` into a
  ||| `ByteAddr`. On `Fix`es it is the operation on the fixnums' values, which
  ||| the producer guarantees is in the fixnum range, and the rendering
  ||| computes it on the words, without untagging where the value encoding has
  ||| an identity for it. There is no arithmetic on `Val`s: a `Val` is narrowed
  ||| to a `Fix` first.
  Arith      : IRCommon.Op.ArithOp -> Location enc -> Opnd enc -> Opnd enc -> Instr enc
  ||| The 128-bit product of two words, into its high word and its low word.
  Mul128     : (high, low : Location enc) -> Opnd enc -> Opnd enc -> Instr enc
  ||| The quotient and the remainder of the 128-bit number of the high and
  ||| the low word by the divisor.
  Div128     : (quotient, remainder : Location enc) -> (high, low, divisor : Opnd enc) -> Instr enc
  ||| Negation or complement of a `W64`.
  Unary      : IRCommon.Op.UnOp -> Location enc -> Location enc -> Instr enc
  ||| `Add`, `Sub` or `Mul`, with the operand types of `Arith`, then a branch
  ||| to the label if the result does not fit: in 64 signed bits for `W64`s,
  ||| in the fixnum range for `Fix`es, which is the fixnum fast path. The
  ||| label is a successor of the block at this instruction, not at the
  ||| block's end.
  ArithOv    : IRCommon.Op.ArithOp -> Location enc -> Opnd enc -> Opnd enc -> Label -> Instr enc
  ||| Narrow a `W64` to the width, then sign- or zero-extend it back to 64
  ||| bits.
  Ext        : Width.SubWord -> (signed : Bool) -> Location enc -> Location enc -> Instr enc
  ||| Double arithmetic on `F64`s.
  FArith     : IRCommon.Op.FOp -> Location enc -> Location enc -> Location enc -> Instr enc
  ||| Double negation.
  FNeg       : Location enc -> Location enc -> Instr enc
  FSqrt      : Location enc -> Location enc -> Instr enc
  ||| Compare two `F64`s; the destination, a `W64`, is 1 or 0.
  FCmp       : IRCommon.Op.Rel -> Location enc -> Location enc -> Location enc -> Instr enc
  ||| Convert between a `W64` and an `F64`.
  Convert    : IRCommon.Op.ConvOp -> Location enc -> Location enc -> Instr enc
  ||| Compare two integers; the destination, a `W64`, is 1 or 0. The operands
  ||| are both `W64`s or both `Fix`es, compared as `Rel` says; a comparison
  ||| never makes a value.
  Cmp        : IRCommon.Op.Rel -> Location enc -> Opnd enc -> Opnd enc -> Instr enc
  ||| Load a word of the given type.
  Load       : IRCommon.Ty enc -> Location enc -> Mem enc -> Instr enc
  ||| Store a register of the given type.
  Store      : IRCommon.Ty enc -> Mem enc -> Location enc -> Instr enc
  ||| Load 8, 16 or 32 bits into a `W64`, zero- or sign-extended: the bytes
  ||| of strings and buffers, the limbs of bignums.
  LoadN      : Width.SubWord -> (signed : Bool) -> Location enc -> Mem enc -> Instr enc
  ||| Store the low 8, 16 or 32 bits of a `W64`.
  StoreN     : Width.SubWord -> Mem enc -> Location enc -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`. The producer guarantees that the
  ||| value is in the fixnum range.
  Tag        : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Location enc -> Location enc -> Instr enc
  ||| The value of a `Fix`, as a `W64`.
  Untag      : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Location enc -> Location enc -> Instr enc
  ||| The fixnum of a `W64`, as a `Fix`, or a branch to the label if the value
  ||| is outside the fixnum range. The label is a successor of the block at
  ||| this instruction, as for `ArithOv`.
  TagOv      : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Location enc -> Location enc -> Label ->
    Instr enc
  ||| A `Val` as the type given, a `Fix` or a `PtrTo k`, which is the
  ||| destination's. No code: the producer guarantees it, after an `IfFixnums`
  ||| or a `Switch` on a header, or from static typing. The only way from a
  ||| `Val` to a fixnum or a pointer.
  Narrow     : IRCommon.Ty enc -> Location enc -> Location enc -> Instr enc
  ||| A `Fix` or a `PtrTo k` as a `Val`. No code.
  Widen      : Location enc -> Location enc -> Instr enc
  ||| A `PtrTo k` as a `W64`. No code. Only the functions of the module that
  ||| implements the runtime's memory interface make one (the term's
  ||| capability index): everywhere else no word can be derived from a
  ||| pointer, which is what lets the rooting stubs cover every pointer
  ||| there is.
  AddrToWord : Location enc -> Location enc -> Instr enc
  ||| A `W64` as a `PtrTo k`. No code. Restricted as `AddrToWord` is.
  WordToAddr : Types.Kind -> Location enc -> Location enc -> Instr enc
  ||| A `Val` as a `W64`, and a `W64` as a `Val`. No code. Restricted as
  ||| `AddrToWord` is.
  ValToWord : Location enc -> Location enc -> Instr enc
  WordToVal : Location enc -> Location enc -> Instr enc
  ||| The header word of the object a `PtrTo k` points to, as a `W64`. For a
  ||| `CONT`, which has no header, it is the layout word.
  LoadHeader : Location enc -> Location enc -> Instr enc
  ||| A part of the header of the object a `PtrTo k` points to, as a `W64`:
  ||| the constructor id of a `CON`, for instance. The pointer's kind is the
  ||| part's kind, which the instruction keeps, so that a pass reads it here
  ||| instead of rebuilding it from the part.
  LoadPart   : {0 k : Types.Kind} -> Types.Header.HeaderPart k -> Location enc -> Location enc -> Instr enc
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
  AllocObj   : {k : Types.Kind} -> Location enc -> Types.Header enc k -> (fields : List (Opnd enc)) ->
               (live : List (Location enc)) -> Instr enc
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
  AllocSized : {k : Types.Kind} -> Location enc -> Types.Header.HeaderPart k -> (count : Location enc) ->
               (fill : Maybe (Opnd enc)) -> (live : List (Location enc)) -> Instr enc
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
  DirectCall : Name -> List (Opnd enc) -> (results : List (Location enc)) -> (mayCollect : Bool) ->
               (live : List (Location enc)) -> Instr enc
  ||| A pinned register's value, and setting it.
  GetPinned  : IRCommon.Pinned -> (result : Location enc) -> Instr enc
  SetPinned  : IRCommon.Pinned -> Opnd enc -> Instr enc
  ||| A system call: its number, then its arguments, giving its result, by
  ||| the platform's convention; never a call of a function.
  SystemCall : (result : Location enc) -> List (Opnd enc) -> Instr enc
  ||| Copy a register to another of the same type: a jump's arguments into
  ||| its block's parameters.
  Move       : Location enc -> Location enc -> Instr enc
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
instrName (CodeOf _ _) = "CodeOf"
instrName (StaticAddr _ _) = "StaticAddr"
instrName (AreaAddr _ _) = "AreaAddr"
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
instrName (Move _ _) = "Move"
instrName (Loc _) = "Loc"
instrName (Comment _) = "Comment"

||| The registers the instruction names, its destinations, its operands'
||| and its memory operands', and those it keeps live: each as often as it
||| names it, in no order to rely on.
export
instrRegs : Instr enc -> List (Location enc)
instrRegs i = case i of
  Const d _ => [d]
  FConst d _ => [d]
  CodeOf d _ => [d]
  StaticAddr d _ => [d]
  AreaAddr d _ => [d]
  Arith _ d x y => d :: Opnd.opRegs x ++ Opnd.opRegs y
  Mul128 h l x y => h :: l :: Opnd.opRegs x ++ Opnd.opRegs y
  Div128 q r h l x => q :: r :: Opnd.opRegs h ++ Opnd.opRegs l ++ Opnd.opRegs x
  Unary _ d x => [d, x]
  ArithOv _ d x y _ => d :: Opnd.opRegs x ++ Opnd.opRegs y
  Ext _ _ d x => [d, x]
  FArith _ d x y => [d, x, y]
  FNeg d x => [d, x]
  FSqrt d x => [d, x]
  FCmp _ d x y => [d, x, y]
  Convert _ d x => [d, x]
  Cmp _ d x y => d :: Opnd.opRegs x ++ Opnd.opRegs y
  Load _ d m => d :: memRegs m
  Store _ m x => x :: memRegs m
  LoadN _ _ d m => d :: memRegs m
  StoreN _ m x => x :: memRegs m
  Tag d x => [d, x]
  Untag d x => [d, x]
  TagOv d x _ => [d, x]
  Narrow _ d x => [d, x]
  Widen d x => [d, x]
  AddrToWord d x => [d, x]
  WordToAddr _ d x => [d, x]
  ValToWord d x => [d, x]
  WordToVal d x => [d, x]
  LoadHeader d x => [d, x]
  LoadPart _ d x => [d, x]
  AllocObj d _ fs live => d :: Opnd.opsRegs fs live
  AllocSized d _ count fill live => d :: count :: maybe [] Opnd.opRegs fill ++ live
  DirectCall _ args ds _ live => ds ++ Opnd.opsRegs args live
  GetPinned _ d => [d]
  SetPinned _ x => Opnd.opRegs x
  SystemCall d args => d :: Opnd.opsRegs args []
  Move d x => [d, x]
  Loc _ => []
  Comment _ => []
  where
    memRegs : Mem enc -> List (Location enc)
    memRegs m = m.base :: maybe [] (\r => [r]) m.index

||| What an instruction reads, its register operands, in the order of its
||| fields, a memory operand's base before its index: not the registers its
||| `live` list keeps.
export
operands : Instr enc -> List (Location enc)
operands i = case i of
  Arith _ _ x y => Opnd.opsRegs [x, y] []
  Mul128 _ _ x y => Opnd.opsRegs [x, y] []
  Div128 _ _ h l x => Opnd.opsRegs [h, l, x] []
  Unary _ _ x => [x]
  ArithOv _ _ x y _ => Opnd.opsRegs [x, y] []
  Ext _ _ _ x => [x]
  FArith _ _ x y => [x, y]
  FNeg _ x => [x]
  FSqrt _ x => [x]
  FCmp _ _ x y => [x, y]
  Convert _ _ x => [x]
  Cmp _ _ x y => Opnd.opsRegs [x, y] []
  Load _ _ m => memRegs m
  Store _ m x => x :: memRegs m
  LoadN _ _ _ m => memRegs m
  StoreN _ m x => x :: memRegs m
  Tag _ x => [x]
  Untag _ x => [x]
  TagOv _ x _ => [x]
  Narrow _ _ x => [x]
  Widen _ x => [x]
  AddrToWord _ x => [x]
  WordToAddr _ _ x => [x]
  ValToWord _ x => [x]
  WordToVal _ x => [x]
  LoadHeader _ x => [x]
  LoadPart _ _ x => [x]
  AllocObj _ _ fs _ => Opnd.opsRegs fs []
  AllocSized _ _ count fill _ => count :: maybe [] Opnd.opRegs fill
  DirectCall _ args _ _ _ => Opnd.opsRegs args []
  SetPinned _ x => Opnd.opRegs x
  SystemCall _ args => Opnd.opsRegs args []
  Move _ x => [x]
  _ => []
  where
    memRegs : Mem enc -> List (Location enc)
    memRegs m = m.base :: maybe [] (\r => [r]) m.index

||| What an instruction writes, in the order of its fields.
export
results : Instr enc -> List (Location enc)
results i = case i of
  Mul128 h l _ _ => [h, l]
  Div128 q r _ _ _ => [q, r]
  Store _ _ _ => []
  StoreN _ _ _ => []
  DirectCall _ _ ds _ _ => ds
  SetPinned _ _ => []
  Loc _ => []
  Comment _ => []
  _ => take 1 (instrRegs i)

||| The instruction with its register operands replaced, in the order
||| `operands` lists them, by as many locations; a register operand the list
||| has no location for stays.
export
withOperands : List (Location enc) -> Instr enc -> Instr enc
withOperands rs i = case i of
  Arith o d x y => let (x', rs1) = opnd rs x; (y', _) = opnd rs1 y in Arith o d x' y'
  Mul128 h l x y => let (x', rs1) = opnd rs x; (y', _) = opnd rs1 y in Mul128 h l x' y'
  Div128 q r h l x =>
    let (h', rs1) = opnd rs h; (l', rs2) = opnd rs1 l; (x', _) = opnd rs2 x in Div128 q r h' l' x'
  Unary o d x => Unary o d (loc rs x)
  ArithOv o d x y l => let (x', rs1) = opnd rs x; (y', _) = opnd rs1 y in ArithOv o d x' y' l
  Ext w s d x => Ext w s d (loc rs x)
  FArith o d x y => FArith o d (loc rs x) (loc (drop 1 rs) y)
  FNeg d x => FNeg d (loc rs x)
  FSqrt d x => FSqrt d (loc rs x)
  FCmp r d x y => FCmp r d (loc rs x) (loc (drop 1 rs) y)
  Convert c d x => Convert c d (loc rs x)
  Cmp r d x y => let (x', rs1) = opnd rs x; (y', _) = opnd rs1 y in Cmp r d x' y'
  Load t d m => Load t d (fst (mem rs m))
  Store t m x => Store t (fst (mem (drop 1 rs) m)) (loc rs x)
  LoadN w s d m => LoadN w s d (fst (mem rs m))
  StoreN w m x => StoreN w (fst (mem (drop 1 rs) m)) (loc rs x)
  Tag d x => Tag d (loc rs x)
  Untag d x => Untag d (loc rs x)
  TagOv d x l => TagOv d (loc rs x) l
  Narrow t d x => Narrow t d (loc rs x)
  Widen d x => Widen d (loc rs x)
  AddrToWord d x => AddrToWord d (loc rs x)
  WordToAddr k d x => WordToAddr k d (loc rs x)
  ValToWord d x => ValToWord d (loc rs x)
  WordToVal d x => WordToVal d (loc rs x)
  LoadHeader d x => LoadHeader d (loc rs x)
  LoadPart p d x => LoadPart p d (loc rs x)
  AllocObj d h fs live => AllocObj d h (opnds rs fs) live
  AllocSized d p count fill live =>
    AllocSized d p (loc rs count) (map (fst . opnd (drop 1 rs)) fill) live
  DirectCall f args ds m live => DirectCall f (opnds rs args) ds m live
  SetPinned p x => SetPinned p (fst (opnd rs x))
  SystemCall d args => SystemCall d (opnds rs args)
  Move d x => Move d (loc rs x)
  _ => i
  where
    -- the next location for a register, the rest of the list after it
    loc : List (Location enc) -> Location enc -> Location enc
    loc (r :: _) _ = r
    loc [] x = x

    opnd : List (Location enc) -> Opnd enc -> (Opnd enc, List (Location enc))
    opnd (r :: rs') (Opnd.R _) = (Opnd.R r, rs')
    opnd rs' o = (o, rs')

    opnds : List (Location enc) -> List (Opnd enc) -> List (Opnd enc)
    opnds _ [] = []
    opnds rs' (o :: os) = let (o', rs'') = opnd rs' o in o' :: opnds rs'' os

    mem : List (Location enc) -> Mem enc -> (Mem enc, List (Location enc))
    mem [] m = (m, [])
    mem (b :: rs') m = case m.index of
      Nothing => ({ base := b } m, rs')
      Just _ => case rs' of
        (ix :: rs'') => ({ base := b, index := Just ix } m, rs'')
        [] => ({ base := b } m, [])

||| The instruction with its results replaced, in the order `results` lists
||| them, by as many locations; a result the list has no location for stays.
export
withResults : List (Location enc) -> Instr enc -> Instr enc
withResults [] i = i
withResults rs@(r :: _) i = case i of
  Mul128 h l x y => Mul128 r (fromMaybe l (getAt 1 rs)) x y
  Div128 q rm h l x => Div128 r (fromMaybe rm (getAt 1 rs)) h l x
  Store _ _ _ => i
  StoreN _ _ _ => i
  DirectCall f args ds m live => DirectCall f args (zipWith const rs ds ++ drop (length rs) ds) m live
  SetPinned _ _ => i
  Loc _ => i
  Comment _ => i
  Const _ c => Const r c
  FConst _ c => FConst r c
  CodeOf _ n => CodeOf r n
  StaticAddr _ n => StaticAddr r n
  AreaAddr _ a => AreaAddr r a
  Arith o _ x y => Arith o r x y
  Unary o _ x => Unary o r x
  ArithOv o _ x y l => ArithOv o r x y l
  Ext w s _ x => Ext w s r x
  FArith o _ x y => FArith o r x y
  FNeg _ x => FNeg r x
  FSqrt _ x => FSqrt r x
  FCmp rl _ x y => FCmp rl r x y
  Convert c _ x => Convert c r x
  Cmp rl _ x y => Cmp rl r x y
  Load t _ m => Load t r m
  LoadN w s _ m => LoadN w s r m
  Tag _ x => Tag r x
  Untag _ x => Untag r x
  TagOv _ x l => TagOv r x l
  Narrow t _ x => Narrow t r x
  Widen _ x => Widen r x
  AddrToWord _ x => AddrToWord r x
  WordToAddr k _ x => WordToAddr k r x
  ValToWord _ x => ValToWord r x
  WordToVal _ x => WordToVal r x
  LoadHeader _ x => LoadHeader r x
  LoadPart p _ x => LoadPart p r x
  AllocObj _ h fs live => AllocObj r h fs live
  AllocSized _ p count fill live => AllocSized r p count fill live
  GetPinned p _ => GetPinned p r
  SystemCall _ args => SystemCall r args
  Move _ x => Move r x
