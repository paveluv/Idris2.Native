||| The term IR's bodies (`Body`): instructions, join points and terminators,
||| in scope.
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Body

import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.OvOp
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.Var

import Core.Name
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.Vect
import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Data.Distinct
import Native.HeapObj.Enc as HeapObj
import Native.HeapObj.ValEnc

%default total

||| Whether the keys of a switch on the type are its values: a `Fix`'s are
||| fixnums.
public export
keysFit : IRCommon.Ty enc -> List Int64 -> Bool
keysFit (IRCommon.Ty.Fix {fx}) ks = all (\k => HeapObj.ValEnc.inFixnumRange (cast k)) ks
keysFit _ _ = True

||| A body of a function of convention `c` that may (`m`) convert between
||| words and addresses, with the blocks `ls` (each its parameters' types)
||| and the variables `ctx` in scope.
public export
data Body : Decls enc -> IRCommon.Conv enc -> Bool -> List (List (IRCommon.Ty enc)) -> List (IRCommon.Ty enc) ->
  Type where
  Bind : {ts : List (IRCommon.Ty enc)} -> Instr d m (Var ctx) ts -> Body d c m ls (ts ++ ctx) -> Body d c m ls ctx
  ||| A join point: `block`, with parameters `ps`, which may jump to itself
  ||| (a loop); then `rest`, from which it is reached.
  Join : (ps : List (IRCommon.Ty enc)) -> (block : Body d c m (ps :: ls) (ps ++ ctx)) ->
         (rest : Body d c m (ps :: ls) ctx) -> Body d c m ls ctx
  Jump : Var ls ps -> All (Opnd (Var ctx)) ps -> Body d c m ls ctx
  ||| Compare two integers and branch.
  Branch : {auto 0 int : IsInt t} -> IRCommon.Op.Rel -> Opnd (Var ctx) t -> Opnd (Var ctx) t ->
           (yes, no : Body d c m ls ctx) -> Body d c m ls ctx
  ||| Whether every one of the values, at least one, is a fixnum; the yes
  ||| branch has them as `Fix`es.
  IfFixnums : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
              {n : Nat} -> Vect (S n) (Opnd (Var ctx) IRCommon.Ty.Val) ->
              (yes : Body d c m ls (replicate (S n) (IRCommon.Ty.Fix {enc}) ++ ctx)) ->
              (no : Body d c m ls ctx) -> Body d c m ls ctx
  ||| Integer arithmetic, or the overflow branch when the result does not
  ||| fit: 64 signed bits for `W64`s, the fixnum range for `Fix`es.
  ArithOv : {t : IRCommon.Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Opnd (Var ctx) t -> Opnd (Var ctx) t ->
            (ok : Body d c m ls (t :: ctx)) ->
            (overflow : Body d c m ls ctx) -> Body d c m ls ctx
  ||| The fixnum of a word, or the overflow branch when it is out of range.
  TagOv : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
          Opnd (Var ctx) IRCommon.Ty.W64 -> (ok : Body d c m ls (IRCommon.Ty.Fix {enc} :: ctx)) ->
            (overflow : Body d c m ls ctx) -> Body d c m ls ctx
  ||| A branch on an integer to the case of its key, else to the default.
  Switch : {auto 0 int : IsInt t} -> Opnd (Var ctx) t -> (keys : List Int64) ->
           {auto 0 ok : So (distinct keys && keysFit t keys)} ->
           All (\_ => Body d c m ls ctx) keys -> (dflt : Body d c m ls ctx) -> Body d c m ls ctx
  Call : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> All (Opnd (Var ctx)) ps ->
         (resume : Body d IRCommon.Conv.CPS m ls (IRCommon.Ty.Val :: ctx)) ->
         Body d IRCommon.Conv.CPS m ls ctx
  TailCall : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> All (Opnd (Var ctx)) ps ->
             Body d IRCommon.Conv.CPS m ls ctx
  ||| Apply a closure to one argument, through the runtime's apply routine.
  Apply : (fn, arg : Opnd (Var ctx) IRCommon.Ty.Val) ->
          (resume : Body d IRCommon.Conv.CPS m ls (IRCommon.Ty.Val :: ctx)) -> Body d IRCommon.Conv.CPS m ls ctx
  TailApply : (fn, arg : Opnd (Var ctx) IRCommon.Ty.Val) -> Body d IRCommon.Conv.CPS m ls ctx
  Return : Opnd (Var ctx) IRCommon.Ty.Val -> Body d IRCommon.Conv.CPS m ls ctx
  ||| Jump to a code address with arguments, under the current continuation:
  ||| the runtime's one way into Idris code.
  Enter : Opnd (Var ctx) IRCommon.Ty.W64 -> List (Opnd (Var ctx) IRCommon.Ty.Val) -> Body d c m ls ctx
  Ret : All (Opnd (Var ctx)) rs -> Body d (IRCommon.Conv.Direct rs col) m ls ctx
  Crash : String -> Body d c m ls ctx
  ||| Exit with the abort status: a construct the backend does not lower yet.
  Unsupported : String -> Body d c m ls ctx
