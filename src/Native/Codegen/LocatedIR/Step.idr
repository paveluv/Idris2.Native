||| A step of a block of the located IR (`Step`): an operation, which
||| realises a definition of the term, or a shuffle, which register
||| allocation inserts, of a value from one location to another or into
||| one.
|||
||| Part of the located IR (`Native.Codegen.LocatedIR.Program` says what it
||| is).
module Native.Codegen.LocatedIR.Step

import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Location

import Core.Name
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Types.Enc as Types

%default total

||| One copy of a parallel move (`Par`): a destination, and its source, of
||| one type.
public export
data Copy : Types.Enc -> Type where
  MkCopy : {0 t : IRCommon.Ty enc} -> (dest, source : Location enc t) -> Copy enc

||| What register allocation puts into a location where the term reads it
||| from no register: an immediate, as the term's operand writes it, into a
||| `W64`, a `Val` or a `Fix`, or a byte address; or a static's address,
||| into a `Val` or a pointer to its kind. Into a `W64` an immediate is the
||| word itself; into a `Val` or a `Fix` the integer, whose word the
||| rendering takes from the value encoding (`valWord` in
||| `HeapObj.ValEnc`), so that the IR is the same under every value
||| encoding; as a `Val`, 0 is also the erased value.
public export
data Materialised = Immediate Int64 | StaticAddress Name

public export
Show Materialised where
  show (Immediate i) = "#" ++ show i
  show (StaticAddress s) = "@" ++ show s

||| A step: an operation, `Op`, the instruction that realises the term's
||| definition of number `def`, as register allocation numbers the term's
||| definitions (`Native.Codegen.RegAlloc`); or a shuffle, which realises
||| none, and which the allocation check follows by its own rule: a move of
||| a location to another of its type, or, for a retyping, of the type it
||| is read as; a parallel move, every destination given its source's value
||| from before any destination is written, the destinations distinct
||| places, a jump's arguments into its block's parameters, which the local
||| assignment makes moves (`Native.Codegen.Sequentialise`), so that no
||| rendering sees one; and a value put into a location (`Materialised`).
public export
data Step : Types.Enc -> Type where
  Op : (def : Nat) -> Instr enc -> Step enc
  Move : {0 t : IRCommon.Ty enc} -> Location enc t -> Location enc t -> Step enc
  Par : List (Copy enc) -> Step enc
  Remat : {0 t : IRCommon.Ty enc} -> Location enc t -> Materialised -> Step enc

||| A short name for messages.
public export
stepName : Step enc -> String
stepName (Op _ i) = Instr.instrName i
stepName (Move _ _) = "Move"
stepName (Par _) = "Par"
stepName (Remat _ _) = "Remat"

||| What a step reads, its register operands, in the order of their
||| fields: an operation's (`Instr.operands`), a move's source, a parallel
||| move's sources.
export
operands : Step enc -> List (Location.Place enc)
operands (Op _ i) = Instr.operands i
operands (Move _ x) = [Location.At x]
operands (Par cs) = map (\(MkCopy _ x) => Location.At x) cs
operands (Remat _ _) = []

||| What a step writes, in the order of their fields.
export
results : Step enc -> List (Location.Place enc)
results (Op _ i) = Instr.results i
results (Move d _) = [Location.At d]
results (Par cs) = map (\(MkCopy d _) => Location.At d) cs
results (Remat d _) = [Location.At d]

||| The registers the step names: its results, its operands, and those an
||| operation keeps live (`Instr.instrRegs`).
export
places : Step enc -> List (Location.Place enc)
places (Op _ i) = Instr.instrRegs i
places s = results s ++ operands s

||| The step with its register operands replaced by the step of a
||| traversal (`Location.Step`), in the order `operands` lists them.
export
traverseOperands : Location.Step s enc -> s -> Step enc -> (s, Step enc)
traverseOperands f st (Op d i) = let (s1, i') = Instr.traverseOperands f st i in (s1, Op d i')
traverseOperands f st (Move d x) = let (s1, x') = f st x in (s1, Move d x')
traverseOperands f st (Par cs) = let (s1, cs') = copies st cs in (s1, Par cs')
  where
    copies : s -> List (Copy enc) -> (s, List (Copy enc))
    copies st' [] = (st', [])
    copies st' (MkCopy d x :: cs') =
      let (s1, x') = f st' x; (s2, cs'') = copies s1 cs' in (s2, MkCopy d x' :: cs'')
traverseOperands _ st r@(Remat _ _) = (st, r)

||| The step with its results replaced by the step of a traversal, in the
||| order `results` lists them.
export
traverseResults : Location.Step s enc -> s -> Step enc -> (s, Step enc)
traverseResults f st (Op d i) = let (s1, i') = Instr.traverseResults f st i in (s1, Op d i')
traverseResults f st (Move d x) = let (s1, d') = f st d in (s1, Move d' x)
traverseResults f st (Par cs) = let (s1, cs') = copies st cs in (s1, Par cs')
  where
    copies : s -> List (Copy enc) -> (s, List (Copy enc))
    copies st' [] = (st', [])
    copies st' (MkCopy d x :: cs') =
      let (s1, d') = f st' d; (s2, cs'') = copies s1 cs' in (s2, MkCopy d' x :: cs'')
traverseResults f st (Remat d m) = let (s1, d') = f st d in (s1, Remat d' m)
