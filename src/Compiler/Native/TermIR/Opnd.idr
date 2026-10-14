||| The term IR's operands (`Opnd`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Opnd

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Ty
import Data.List.Quantifiers
import Data.So

%default total

||| An operand: a variable, or an immediate that encodes as its type.
public export
data Opnd : (var : Ty enc -> Type) -> Ty enc -> Type where
  V : var t -> Opnd var t
  ||| A word.
  W : Int64 -> Opnd var W64
  ||| A fixnum, as a `Fix`.
  Fx : {auto 0 fx : HasFixnums enc.val} ->
       (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd var (Fix {enc})
  ||| A fixnum, as a `Val`.
  Vx : {auto 0 fx : HasFixnums enc.val} ->
       (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd var Val
  ||| The erased value, as a `Val`, under every encoding.
  Erased : Opnd var Val

||| The operands, each replaced, effectfully.
public export
traverseAll : Applicative f => ({0 t : Ty enc} -> Opnd v t -> f (Opnd w t)) -> All (Opnd v) ts -> f (All (Opnd w) ts)
traverseAll g [] = pure []
traverseAll g (x :: xs) = [| g x :: traverseAll g xs |]
