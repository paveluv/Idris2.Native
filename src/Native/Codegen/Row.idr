||| Where the rendering of an instruction wants its register operands and
||| its results (`Row`), on a target: each in one of the target's
||| allocatable registers of a class, by its index among them in the
||| target's description (`Native.Codegen.RegDesc`), which register
||| allocation puts it in before the instruction and takes it from after;
||| or anywhere, which the rendering reads or writes itself, through a
||| register of its own where it is a slot.
module Native.Codegen.Row

import Native.Rep

%default total

||| A register of the class, by its index; or anywhere. A value of the
||| other class, such as a double the rendering moves as its bits through a
||| word register, stays where it is.
public export
data Want = InRegister Rep.RegClass Nat | Anywhere

||| The register operands' wants, in the order the located IR lists them
||| (`LocatedIR.Instr.operands`), and the results' (`results`); an operand
||| or a result past a list is wanted anywhere.
public export
record Row where
  constructor MkRow
  operands : List Want
  results : List Want

||| A row that wants every operand and result anywhere.
public export
anywhere : Row
anywhere = MkRow [] []
