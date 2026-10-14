||| The term IR's instructions (`Instr`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Instr

import Compiler.Native.TermIR.Decls
import Compiler.Native.TermIR.FieldTys
import Compiler.Native.TermIR.IsInt
import Compiler.Native.TermIR.Mem
import Compiler.Native.TermIR.Opnd
import Compiler.Native.TermIR.Sig
import Compiler.Native.TermIR.Sizes
import Compiler.Native.TermIR.StaticSig
import Compiler.Native.TermIR.Var

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Area
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Intrinsic
import Compiler.Native.IRCommon.Operators.ArithOp
import Compiler.Native.IRCommon.Operators.ConvOp
import Compiler.Native.IRCommon.Operators.FOp
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.IRCommon.Operators.SubWord
import Compiler.Native.IRCommon.Operators.UnOp
import Compiler.Native.IRCommon.Ty
import Core.FC
import Core.Name
import Data.List.Quantifiers
import Data.So

%default total

||| What a conversion takes.
public export
convFrom : ConvOp -> Ty enc
convFrom I2F = W64
convFrom F2I = F64
convFrom FBits = F64
convFrom BitsF = W64

||| What a conversion makes.
public export
convTo : ConvOp -> Ty enc
convTo I2F = F64
convTo F2I = W64
convTo FBits = W64
convTo BitsF = F64

||| An instruction of a function that may (`True`) or may not convert between
||| words and addresses, with the types of the results it binds.
public export
data Instr : Decls enc -> Bool -> (var : Ty enc -> Type) -> List (Ty enc) -> Type where
  FConst : Double -> Instr d m var [F64]
  ||| The entry address of a CPS function of the program: a closure's code.
  CodeAddr : Var d.sigs (MkSig n CPS ps cv) -> Instr d m var [W64]
  ||| The address of a static object, as a pointer to its kind.
  StaticAddr : Var d.statics (MkStaticSig s k) -> Instr d m var [PtrTo k]
  AreaAddr : Area -> Instr d m var [W64]
  ||| Integer arithmetic on two `W64`s or two `Fix`es; on `Fix`es the
  ||| producer guarantees the result is a fixnum.
  Arith : {auto 0 int : IsInt t} -> ArithOp -> Opnd var t -> Opnd var t -> Instr d m var [t]
  Unary : UnOp -> Opnd var W64 -> Instr d m var [W64]
  ||| Narrow a word to the width, then extend it back, signed or not.
  Ext : SubWord -> (signed : Bool) -> Opnd var W64 -> Instr d m var [W64]
  FArith : FOp -> Opnd var F64 -> Opnd var F64 -> Instr d m var [F64]
  FNeg : Opnd var F64 -> Instr d m var [F64]
  ||| Compare two doubles: 1 or 0.
  FCmp : Rel -> Opnd var F64 -> Opnd var F64 -> Instr d m var [W64]
  Convert : (op : ConvOp) -> Opnd var (convFrom op) -> Instr d m var [convTo op]
  ||| Compare two integers: 1 or 0.
  Cmp : {auto 0 int : IsInt t} -> Rel -> Opnd var t -> Opnd var t -> Instr d m var [W64]
  Load : (t : Ty enc) -> Mem var -> Instr d m var [t]
  Store : (t : Ty enc) -> Mem var -> Opnd var t -> Instr d m var []
  ||| Load 8, 16 or 32 bits, extended to a word.
  LoadN : SubWord -> (signed : Bool) -> Mem var -> Instr d m var [W64]
  ||| Store a word's low 8, 16 or 32 bits.
  StoreN : SubWord -> Mem var -> Opnd var W64 -> Instr d m var []
  ||| The fixnum of a word the producer knows is in range.
  Tag : {auto 0 fx : HasFixnums enc.val} -> Opnd var W64 -> Instr d m var [Fix {enc}]
  Untag : {auto 0 fx : HasFixnums enc.val} -> Opnd var (Fix {enc}) -> Instr d m var [W64]
  ||| A `Val` the producer knows is a fixnum.
  NarrowFix : {auto 0 fx : HasFixnums enc.val} -> Opnd var Val -> Instr d m var [Fix {enc}]
  ||| A `Val` the producer knows points to an object of the kind.
  NarrowPtr : (k : Kind) -> Opnd var Val -> Instr d m var [PtrTo k]
  WidenFix : {auto 0 fx : HasFixnums enc.val} -> Opnd var (Fix {enc}) -> Instr d m var [Val]
  WidenPtr : Opnd var (PtrTo k) -> Instr d m var [Val]
  AddrToWord : Opnd var (PtrTo k) -> Instr d True var [W64]
  WordToAddr : (k : Kind) -> Opnd var W64 -> Instr d True var [PtrTo k]
  ||| The header word of an object; a continuation's layout word.
  LoadHeader : Opnd var (PtrTo k) -> Instr d m var [W64]
  LoadPart : {0 k : Kind} -> HeaderPart k -> Opnd var (PtrTo k) -> Instr d m var [W64]
  ||| A whole object in one step, from a header known when the program is
  ||| compiled and its fields.
  AllocObj : {k : Kind} -> (h : Header enc k) -> {auto 0 ok : So (wellFormed h)} ->
             All (Opnd var) (fieldTys h) -> Instr d m var [PtrTo k]
  ||| A whole object of a size known at run time: the count is the part.
  AllocSized : {k : Kind} -> (p : HeaderPart k) -> {auto 0 sizes : Sizes p} -> (count : Opnd var W64) ->
               Fill var p -> Instr d m var [PtrTo k]
  ||| A machine call of a Direct function, binding its results.
  DirectCall : Var d.sigs (MkSig n (Direct rs col) ps cv) -> All (Opnd var) ps -> Instr d m var rs
  ||| An intrinsic, on what it takes, binding what it gives.
  Intrinsic : (i : Intrinsic) -> All (Opnd var) (params i) -> Instr d m var (results i)
  ||| The source location of what follows.
  Loc : FC -> Instr d m var []
  Comment : String -> Instr d m var []

||| The instruction with each operand replaced, effectfully: how a pass
||| changes the representation of variables.
public export
traverseInstr : Applicative f => ({0 t : Ty enc} -> Opnd v t -> f (Opnd w t)) -> Instr d m v ts -> f (Instr d m w ts)
traverseInstr g (FConst x) = pure (FConst x)
traverseInstr g (CodeAddr r) = pure (CodeAddr r)
traverseInstr g (StaticAddr r) = pure (StaticAddr r)
traverseInstr g (AreaAddr a) = pure (AreaAddr a)
traverseInstr g (Arith {int} o x y) = [| (\x', y' => Arith {int} o x' y') (g x) (g y) |]
traverseInstr g (Unary o x) = Unary o <$> g x
traverseInstr g (Ext w s x) = Ext w s <$> g x
traverseInstr g (FArith o x y) = [| FArith (pure o) (g x) (g y) |]
traverseInstr g (FNeg x) = FNeg <$> g x
traverseInstr g (FCmp r x y) = [| FCmp (pure r) (g x) (g y) |]
traverseInstr g (Convert op x) = Convert op <$> g x
traverseInstr g (Cmp {int} r x y) = [| (\x', y' => Cmp {int} r x' y') (g x) (g y) |]
traverseInstr g (Load t mem) = Load t <$> traverseMem g mem
traverseInstr g (Store t mem x) = [| (\mem', x' => Store t mem' x') (traverseMem g mem) (g x) |]
traverseInstr g (LoadN w s mem) = LoadN w s <$> traverseMem g mem
traverseInstr g (StoreN w mem x) = [| StoreN (pure w) (traverseMem g mem) (g x) |]
traverseInstr g (Tag {fx} x) = Tag {fx} <$> g x
traverseInstr g (Untag {fx} x) = Untag {fx} <$> g x
traverseInstr g (NarrowFix {fx} x) = NarrowFix {fx} <$> g x
traverseInstr g (NarrowPtr k x) = NarrowPtr k <$> g x
traverseInstr g (WidenFix {fx} x) = WidenFix {fx} <$> g x
traverseInstr g (WidenPtr x) = WidenPtr <$> g x
traverseInstr g (AddrToWord x) = AddrToWord <$> g x
traverseInstr g (WordToAddr k x) = WordToAddr k <$> g x
traverseInstr g (LoadHeader x) = LoadHeader <$> g x
traverseInstr g (LoadPart p x) = LoadPart p <$> g x
traverseInstr g (AllocObj h {ok} fs) = (\fs' => AllocObj h {ok} fs') <$> traverseAll g fs
traverseInstr g (AllocSized ArrayElems {sizes} c f) = [| (\c', f' => AllocSized ArrayElems {sizes} c' f') (g c) (g f) |]
traverseInstr g (AllocSized StringAscii {sizes} c f) = (\c' => AllocSized StringAscii {sizes} c' f) <$> g c
traverseInstr g (AllocSized StringBytes {sizes} c f) = (\c' => AllocSized StringBytes {sizes} c' f) <$> g c
traverseInstr g (AllocSized StringChars {sizes} c f) = (\c' => AllocSized StringChars {sizes} c' f) <$> g c
traverseInstr g (AllocSized BufferBytes {sizes} c f) = (\c' => AllocSized BufferBytes {sizes} c' f) <$> g c
traverseInstr g (AllocSized ConId {sizes} c f) = (\c' => AllocSized ConId {sizes} c' f) <$> g c
traverseInstr g (AllocSized ConArity {sizes} c f) = (\c' => AllocSized ConArity {sizes} c' f) <$> g c
traverseInstr g (AllocSized ClosureArity {sizes} c f) = (\c' => AllocSized ClosureArity {sizes} c' f) <$> g c
traverseInstr g (AllocSized ClosureFilled {sizes} c f) = (\c' => AllocSized ClosureFilled {sizes} c' f) <$> g c
traverseInstr g (AllocSized BignumNegative {sizes} c f) = (\c' => AllocSized BignumNegative {sizes} c' f) <$> g c
traverseInstr g (AllocSized BignumWords {sizes} c f) = (\c' => AllocSized BignumWords {sizes} c' f) <$> g c
traverseInstr g (DirectCall r xs) = DirectCall r <$> traverseAll g xs
traverseInstr g (Intrinsic i xs) = Intrinsic i <$> traverseAll g xs
traverseInstr g (Loc fc) = pure (Loc fc)
traverseInstr g (Comment s) = pure (Comment s)
