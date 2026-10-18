||| The term IR's instructions (`Instr`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Instr

import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Mem
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.Sizes
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var

import Core.FC
import Core.Name
import Data.Fin
import Data.List
import Data.List.Quantifiers
import Data.So
import Native.Area
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

||| What a conversion takes.
public export
convFrom : IRCommon.Op.ConvOp -> IRCommon.Ty enc
convFrom IRCommon.Op.I2F = IRCommon.Ty.W64
convFrom IRCommon.Op.F2I = IRCommon.Ty.F64
convFrom IRCommon.Op.FBits = IRCommon.Ty.F64
convFrom IRCommon.Op.BitsF = IRCommon.Ty.W64

||| What a conversion makes.
public export
convTo : IRCommon.Op.ConvOp -> IRCommon.Ty enc
convTo IRCommon.Op.I2F = IRCommon.Ty.F64
convTo IRCommon.Op.F2I = IRCommon.Ty.W64
convTo IRCommon.Op.FBits = IRCommon.Ty.W64
convTo IRCommon.Op.BitsF = IRCommon.Ty.F64

||| An instruction of a function that may (`True`) or may not convert between
||| words and addresses, with the types of the results it binds.
public export
data Instr : Decls enc -> Bool -> (var : IRCommon.Ty enc -> Type) -> List (IRCommon.Ty enc) -> Type where
  FConst : Double -> Instr d m var [IRCommon.Ty.F64]
  ||| The entry address of a CPS function of the program: a closure's code.
  CodeAddr : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> Instr d m var [IRCommon.Ty.W64]
  ||| The address of a static object, as a pointer to its kind.
  StaticAddr : Var d.statics (MkStaticSig s k) -> Instr d m var [IRCommon.Ty.PtrTo k]
  AreaAddr : Area -> Instr d m var [IRCommon.Ty.W64]
  ||| The address of a table's rows, which the code generator computed
  ||| (`Native.Table`).
  TableAddr : Name -> Instr d m var [IRCommon.Ty.W64]
  ||| Integer arithmetic on two `W64`s or two `Fix`es; on `Fix`es the
  ||| producer guarantees the result is a fixnum.
  Arith : {auto 0 int : IsInt t} -> IRCommon.Op.ArithOp -> Opnd var t -> Opnd var t -> Instr d m var [t]
  ||| The 128-bit product of two words: its high word, then its low word.
  Mul128 : Opnd var IRCommon.Ty.W64 -> Opnd var IRCommon.Ty.W64 -> Instr d m var [IRCommon.Ty.W64, IRCommon.Ty.W64]
  Unary : IRCommon.Op.UnOp -> Opnd var IRCommon.Ty.W64 -> Instr d m var [IRCommon.Ty.W64]
  ||| Narrow a word to the width, then extend it back, signed or not.
  Ext : IRCommon.Op.SubWord -> (signed : Bool) -> Opnd var IRCommon.Ty.W64 -> Instr d m var [IRCommon.Ty.W64]
  FArith : IRCommon.Op.FOp -> Opnd var IRCommon.Ty.F64 -> Opnd var IRCommon.Ty.F64 -> Instr d m var [IRCommon.Ty.F64]
  FNeg : Opnd var IRCommon.Ty.F64 -> Instr d m var [IRCommon.Ty.F64]
  ||| Compare two doubles: 1 or 0.
  FCmp : IRCommon.Op.Rel -> Opnd var IRCommon.Ty.F64 -> Opnd var IRCommon.Ty.F64 -> Instr d m var [IRCommon.Ty.W64]
  Convert : (op : IRCommon.Op.ConvOp) -> Opnd var (convFrom op) -> Instr d m var [convTo op]
  ||| Compare two integers: 1 or 0.
  Cmp : {auto 0 int : IsInt t} -> IRCommon.Op.Rel -> Opnd var t -> Opnd var t -> Instr d m var [IRCommon.Ty.W64]
  Load : (t : IRCommon.Ty enc) -> Mem var -> Instr d m var [t]
  Store : (t : IRCommon.Ty enc) -> Mem var -> Opnd var t -> Instr d m var []
  ||| Load 8, 16 or 32 bits, extended to a word.
  LoadN : IRCommon.Op.SubWord -> (signed : Bool) -> Mem var -> Instr d m var [IRCommon.Ty.W64]
  ||| Store a word's low 8, 16 or 32 bits.
  StoreN : IRCommon.Op.SubWord -> Mem var -> Opnd var IRCommon.Ty.W64 -> Instr d m var []
  ||| The fixnum of a word the producer knows is in range.
  Tag : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Opnd var IRCommon.Ty.W64 ->
        Instr d m var [IRCommon.Ty.Fix {enc}]
  Untag : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Opnd var (IRCommon.Ty.Fix {enc}) ->
          Instr d m var [IRCommon.Ty.W64]
  ||| A `Val` the producer knows is a fixnum.
  NarrowFix : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Opnd var IRCommon.Ty.Val ->
              Instr d m var [IRCommon.Ty.Fix {enc}]
  ||| A `Val` the producer knows points to an object of the kind.
  NarrowPtr : (k : Types.Kind) -> Opnd var IRCommon.Ty.Val -> Instr d m var [IRCommon.Ty.PtrTo k]
  WidenFix : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Opnd var (IRCommon.Ty.Fix {enc}) ->
             Instr d m var [IRCommon.Ty.Val]
  WidenPtr : Opnd var (IRCommon.Ty.PtrTo k) -> Instr d m var [IRCommon.Ty.Val]
  AddrToWord : Opnd var (IRCommon.Ty.PtrTo k) -> Instr d True var [IRCommon.Ty.W64]
  WordToAddr : (k : Types.Kind) -> Opnd var IRCommon.Ty.W64 -> Instr d True var [IRCommon.Ty.PtrTo k]
  ||| The word a `Val` is, and the `Val` a word is, of any value: restricted
  ||| as `AddrToWord` is.
  ValToWord : Opnd var IRCommon.Ty.Val -> Instr d True var [IRCommon.Ty.W64]
  WordToVal : Opnd var IRCommon.Ty.W64 -> Instr d True var [IRCommon.Ty.Val]
  ||| The header word of an object; a continuation's layout word.
  LoadHeader : Opnd var (IRCommon.Ty.PtrTo k) -> Instr d m var [IRCommon.Ty.W64]
  LoadPart : {0 k : Types.Kind} -> Types.Header.HeaderPart k -> Opnd var (IRCommon.Ty.PtrTo k) ->
             Instr d m var [IRCommon.Ty.W64]
  ||| A whole object in one step, from a header known when the program is
  ||| compiled and its fields.
  AllocObj : {k : Types.Kind} -> (h : Types.Header enc k) -> {auto 0 ok : So (wellFormed h)} ->
             All (Opnd var) (fieldTys h) -> Instr d m var [IRCommon.Ty.PtrTo k]
  ||| A whole object of a size known at run time: the count is the part.
  AllocSized : {k : Types.Kind} -> (p : Types.Header.HeaderPart k) -> {auto 0 sizes : Sizes p} ->
               (count : Opnd var IRCommon.Ty.W64) ->
               Sizes.Fill var p -> Instr d m var [IRCommon.Ty.PtrTo k]
  ||| A machine call of a Direct function, binding its results.
  DirectCall : Var d.sigs (MkSig n (IRCommon.Conv.Direct rs col) ps cv) -> All (Opnd var) ps -> Instr d m var rs
  ||| A pinned register's value, and setting it.
  GetPinned : (r : IRCommon.Pinned) -> Instr d m var [IRCommon.Pinned.pinnedTy r]
  SetPinned : (r : IRCommon.Pinned) -> Opnd var (IRCommon.Pinned.pinnedTy r) -> Instr d m var []
  ||| One system call of so many arguments, at most six: its number, then the
  ||| arguments, giving its result, by the platform's convention. A
  ||| collection never starts in a system call.
  SystemCall : (n : Fin 7) -> All (Opnd var) (replicate (S (finToNat n)) IRCommon.Ty.W64) ->
               Instr d m var [IRCommon.Ty.W64]
  ||| The source location of what follows.
  Loc : FC -> Instr d m var []
  Comment : String -> Instr d m var []

||| The instruction with each operand replaced, effectfully: how a pass
||| changes the representation of variables.
public export
traverseInstr : Applicative f => ({0 t : IRCommon.Ty enc} -> Opnd v t -> f (Opnd w t)) -> Instr d m v ts ->
                f (Instr d m w ts)
traverseInstr g (FConst x) = pure (FConst x)
traverseInstr g (CodeAddr r) = pure (CodeAddr r)
traverseInstr g (StaticAddr r) = pure (StaticAddr r)
traverseInstr g (AreaAddr a) = pure (AreaAddr a)
traverseInstr g (TableAddr n) = pure (TableAddr n)
traverseInstr g (Arith {int} o x y) = [| (\x', y' => Arith {int} o x' y') (g x) (g y) |]
traverseInstr g (Mul128 x y) = [| Mul128 (g x) (g y) |]
traverseInstr g (Unary o x) = Unary o <$> g x
traverseInstr g (Ext w s x) = Ext w s <$> g x
traverseInstr g (FArith o x y) = [| FArith (pure o) (g x) (g y) |]
traverseInstr g (FNeg x) = FNeg <$> g x
traverseInstr g (FCmp r x y) = [| FCmp (pure r) (g x) (g y) |]
traverseInstr g (Convert op x) = Convert op <$> g x
traverseInstr g (Cmp {int} r x y) = [| (\x', y' => Cmp {int} r x' y') (g x) (g y) |]
traverseInstr g (Load t mem) = Load t <$> Mem.traverseMem g mem
traverseInstr g (Store t mem x) = [| (\mem', x' => Store t mem' x') (Mem.traverseMem g mem) (g x) |]
traverseInstr g (LoadN w s mem) = LoadN w s <$> Mem.traverseMem g mem
traverseInstr g (StoreN w mem x) = [| StoreN (pure w) (Mem.traverseMem g mem) (g x) |]
traverseInstr g (Tag {fx} x) = Tag {fx} <$> g x
traverseInstr g (Untag {fx} x) = Untag {fx} <$> g x
traverseInstr g (NarrowFix {fx} x) = NarrowFix {fx} <$> g x
traverseInstr g (NarrowPtr k x) = NarrowPtr k <$> g x
traverseInstr g (WidenFix {fx} x) = WidenFix {fx} <$> g x
traverseInstr g (WidenPtr x) = WidenPtr <$> g x
traverseInstr g (AddrToWord x) = AddrToWord <$> g x
traverseInstr g (WordToAddr k x) = WordToAddr k <$> g x
traverseInstr g (ValToWord x) = ValToWord <$> g x
traverseInstr g (WordToVal x) = WordToVal <$> g x
traverseInstr g (LoadHeader x) = LoadHeader <$> g x
traverseInstr g (LoadPart p x) = LoadPart p <$> g x
traverseInstr g (AllocObj h {ok} fs) = (\fs' => AllocObj h {ok} fs') <$> Opnd.traverseAll g fs
traverseInstr g (AllocSized Types.Header.ArrayElems {sizes} c f) =
  [| (\c', f' => AllocSized Types.Header.ArrayElems {sizes} c' f') (g c) (g f) |]
traverseInstr g (AllocSized Types.Header.StringAscii {sizes} c f) =
  (\c' => AllocSized Types.Header.StringAscii {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.StringBytes {sizes} c f) =
  (\c' => AllocSized Types.Header.StringBytes {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.StringChars {sizes} c f) =
  (\c' => AllocSized Types.Header.StringChars {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.BufferBytes {sizes} c f) =
  (\c' => AllocSized Types.Header.BufferBytes {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.ConId {sizes} c f) =
  (\c' => AllocSized Types.Header.ConId {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.ConArity {sizes} c f) =
  (\c' => AllocSized Types.Header.ConArity {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.ClosureArity {sizes} c f) =
  (\c' => AllocSized Types.Header.ClosureArity {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.ClosureFilled {sizes} c f) =
  (\c' => AllocSized Types.Header.ClosureFilled {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.BignumNegative {sizes} c f) =
  (\c' => AllocSized Types.Header.BignumNegative {sizes} c' f) <$> g c
traverseInstr g (AllocSized Types.Header.BignumWords {sizes} c f) =
  (\c' => AllocSized Types.Header.BignumWords {sizes} c' f) <$> g c
traverseInstr g (DirectCall r xs) = DirectCall r <$> Opnd.traverseAll g xs
traverseInstr g (GetPinned r) = pure (GetPinned r)
traverseInstr g (SetPinned r x) = SetPinned r <$> g x
traverseInstr g (SystemCall n xs) = SystemCall n <$> Opnd.traverseAll g xs
traverseInstr g (Loc fc) = pure (Loc fc)
traverseInstr g (Comment s) = pure (Comment s)
