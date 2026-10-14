||| The term IR's bodies (`Body`): instructions, join points and terminators,
||| in scope.
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Body

import Compiler.Native.TermIR.Decls
import Compiler.Native.TermIR.Instr
import Compiler.Native.TermIR.IsInt
import Compiler.Native.TermIR.Opnd
import Compiler.Native.TermIR.OvOp
import Compiler.Native.TermIR.Sig
import Compiler.Native.TermIR.Var

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.IRCommon.Ty
import Core.Name
import Data.Distinct
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.Vect

%default total

||| Whether the keys of a switch on the type are its values: a `Fix`'s are
||| fixnums.
public export
keysFit : Ty enc -> List Int64 -> Bool
keysFit (Fix {fx}) ks = all (\k => inFixnumRange (cast k)) ks
keysFit _ _ = True

public export
Op : List (Ty enc) -> Ty enc -> Type
Op ctx = Opnd (Var ctx)

||| A body of a function of convention `c` that may (`m`) convert between
||| words and addresses, with the blocks `ls` (each its parameters' types)
||| and the variables `ctx` in scope.
public export
data Body : Decls enc -> Conv enc -> Bool -> List (List (Ty enc)) -> List (Ty enc) -> Type where
  Bind : {ts : List (Ty enc)} -> Instr d m (Var ctx) ts -> Body d c m ls (ts ++ ctx) -> Body d c m ls ctx
  ||| A join point: `block`, with parameters `ps`, which may jump to itself
  ||| (a loop); then `rest`, from which it is reached.
  Join : (ps : List (Ty enc)) -> (block : Body d c m (ps :: ls) (ps ++ ctx)) ->
         (rest : Body d c m (ps :: ls) ctx) -> Body d c m ls ctx
  Jump : Var ls ps -> All (Op ctx) ps -> Body d c m ls ctx
  ||| Compare two integers and branch.
  Branch : {auto 0 int : IsInt t} -> Rel -> Op ctx t -> Op ctx t -> (yes, no : Body d c m ls ctx) -> Body d c m ls ctx
  ||| Whether every one of the values, at least one, is a fixnum; the yes
  ||| branch has them as `Fix`es.
  IfFixnums : {auto 0 fx : HasFixnums enc.val} ->
              {n : Nat} -> Vect (S n) (Op ctx Val) ->
              (yes : Body d c m ls (replicate (S n) (Fix {enc}) ++ ctx)) ->
              (no : Body d c m ls ctx) -> Body d c m ls ctx
  ||| Integer arithmetic, or the overflow branch when the result does not
  ||| fit: 64 signed bits for `W64`s, the fixnum range for `Fix`es.
  ArithOv : {t : Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Op ctx t -> Op ctx t -> (ok : Body d c m ls (t :: ctx)) ->
            (overflow : Body d c m ls ctx) -> Body d c m ls ctx
  ||| The fixnum of a word, or the overflow branch when it is out of range.
  TagOv : {auto 0 fx : HasFixnums enc.val} ->
          Op ctx W64 -> (ok : Body d c m ls (Fix {enc} :: ctx)) -> (overflow : Body d c m ls ctx) -> Body d c m ls ctx
  ||| A branch on an integer to the case of its key, else to the default.
  Switch : {auto 0 int : IsInt t} -> Op ctx t -> (keys : List Int64) ->
           {auto 0 ok : So (distinct keys && keysFit t keys)} ->
           All (\_ => Body d c m ls ctx) keys -> (dflt : Body d c m ls ctx) -> Body d c m ls ctx
  Call : Var d.sigs (MkSig n CPS ps cv) -> All (Op ctx) ps -> (resume : Body d CPS m ls (Val :: ctx)) ->
         Body d CPS m ls ctx
  TailCall : Var d.sigs (MkSig n CPS ps cv) -> All (Op ctx) ps -> Body d CPS m ls ctx
  ||| Apply a closure to one argument, through the runtime's apply routine.
  Apply : (fn, arg : Op ctx Val) -> (resume : Body d CPS m ls (Val :: ctx)) -> Body d CPS m ls ctx
  TailApply : (fn, arg : Op ctx Val) -> Body d CPS m ls ctx
  Return : Op ctx Val -> Body d CPS m ls ctx
  ||| Jump to a code address with arguments, under the current continuation:
  ||| the runtime's one way into Idris code.
  Enter : Op ctx W64 -> List (Op ctx Val) -> Body d c m ls ctx
  Ret : All (Op ctx) rs -> Body d (Direct rs col) m ls ctx
  Crash : String -> Body d c m ls ctx
  ||| Exit with the abort status: a construct the backend does not lower yet.
  Unsupported : String -> Body d c m ls ctx
