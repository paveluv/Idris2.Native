||| The term IR's memory references (`Mem`).
|||
||| Part of the term IR (`Native.Codegen.TermIR.Program` says what it is).
module Native.Codegen.TermIR.Mem

import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Opnd

import Data.Maybe
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types
import Native.Types.Kind as Types

%default total

||| A memory reference's base: an object pointer or a byte address, never a
||| `Val`, which may be a fixnum, and never a word, which is no address. It
||| says, by its type, the kind of the object, if it is one.
public export
data Base : (var : IRCommon.Ty enc -> Type) -> Maybe Types.Kind -> Type where
  AtBytes : Opnd var IRCommon.Ty.ByteAddr -> Base var Nothing
  AtPtr : {k : Types.Kind} -> Opnd var (IRCommon.Ty.PtrTo k) -> Base var (Just k)

||| What the IR knows of the word a memory reference names: the kind of the
||| object it is in, if its base is an object's, whether an index moves it,
||| and its constant offset.
public export
record Cell where
  constructor MkCell
  object : Maybe Types.Kind
  indexed : Bool
  offset : Int

||| A memory reference: a base, an optional index counting units of the
||| access's width, and a constant byte offset; its type says what is known
||| of the word it names.
public export
data Mem : {0 enc : Types.Enc} -> (var : IRCommon.Ty enc -> Type) -> Cell -> Type where
  MkMem : Base var b -> (index : Maybe (Opnd var IRCommon.Ty.W64)) -> (offset : Int) ->
          Mem var (MkCell b (isJust index) offset)

||| Whether a register of the type may be loaded from the cell, or stored in
||| it: of the type an object of its kind has there, where the kind says
||| (`FieldTys.cellTy`); of any type in memory that holds no object, and
||| where the kind does not say.
public export
admits : Cell -> IRCommon.Ty enc -> Bool
admits (MkCell Nothing _ _) _ = True
admits (MkCell (Just k) i o) t = maybe True (== t) (FieldTys.cellTy k i o)

||| The base with its operand replaced, effectfully.
public export
traverseBase : Applicative f => ({0 t : IRCommon.Ty enc} -> Opnd v t -> f (Opnd w t)) ->
               Base v b ->
               f (Base w b)
traverseBase g (AtBytes x) = AtBytes <$> g x
traverseBase g (AtPtr x) = AtPtr <$> g x

||| The reference with each operand replaced, effectfully: the same cell.
public export
traverseMem : Applicative f => ({0 t : IRCommon.Ty enc} -> Opnd v t -> f (Opnd w t)) -> Mem v c ->
              f (Mem w c)
traverseMem g (MkMem b Nothing o) = (\b' => MkMem b' Nothing o) <$> traverseBase g b
traverseMem g (MkMem b (Just x) o) =
  [| (\b', x' => MkMem b' (Just x') o) (traverseBase g b) (g x) |]
