||| The term IR's operands (`Opnd`).
|||
||| Part of the term IR (`Compiler.Native.TermIR.Program` says what it is).
module Compiler.Native.TermIR.Opnd

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Ty as IRCommon
import Data.List.Quantifiers
import Data.So

%default total

||| An operand: a variable, or an immediate that encodes as its type.
public export
data Opnd : (var : IRCommon.Ty enc -> Type) -> IRCommon.Ty enc -> Type where
  V : var t -> Opnd var t
  ||| A word.
  W : Int64 -> Opnd var IRCommon.Ty.W64
  ||| A fixnum, as a `Fix`.
  Fx : {auto 0 fx : HeapObject.ValEnc.HasFixnums enc.val} ->
       (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd var (IRCommon.Ty.Fix {enc})
  ||| A fixnum, as a `Val`.
  Vx : {auto 0 fx : HeapObject.ValEnc.HasFixnums enc.val} ->
       (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd var IRCommon.Ty.Val
  ||| The erased value, as a `Val`, under every encoding.
  Erased : Opnd var IRCommon.Ty.Val

||| The operands, each replaced, effectfully.
public export
traverseAll : Applicative f => ({0 t : IRCommon.Ty enc} -> Opnd v t -> f (Opnd w t)) -> All (Opnd v) ts -> f (All (Opnd w) ts)
traverseAll g [] = pure []
traverseAll g (x :: xs) = [| g x :: traverseAll g xs |]
