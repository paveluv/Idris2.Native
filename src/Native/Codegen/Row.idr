||| Where the rendering of an instruction wants its register operands and
||| its results (`Row`), on a target: each in one of the target's
||| allocatable registers of a class, by its index among them in the
||| target's description (`Native.Codegen.RegDesc`), which register
||| allocation puts it in before the instruction and takes it from after;
||| or anywhere, which the rendering reads or writes itself, through a
||| register of its own where it is a slot. A row also names every other
||| allocatable register the rendering writes (`clobbers`), so that no
||| value register allocation keeps in one is lost; the x86-64 rendering
||| checks its code against its rows.
module Native.Codegen.Row

import Native.Codegen.RegMask
import Native.Rep

%default total

||| A register of the class, by its index; or anywhere. A value of the
||| other class, such as a double the rendering moves as its bits through a
||| word register, stays where it is.
public export
data Want = InRegister Rep.RegClass Nat | Anywhere

||| The register operands' wants, in the order the located IR lists them
||| (`LocatedIR.Instr.operands`), and the results' (`results`); an operand
||| or a result past a list is wanted anywhere. Then the registers the
||| rendering writes besides its results: those it computes in, the
||| operands it changes in place, and what a callee may write.
public export
record Row where
  constructor MkRow
  operands : List Want
  results : List Want
  clobbers : RegMask

||| The registers of the wants, as a set; a want of anywhere names none.
export
clobbering : List Want -> RegMask
clobbering = foldr (\w, m => RegMask.union (one w) m) RegMask.none
  where
    one : Want -> RegMask
    one (InRegister c i) = RegMask.single c i
    one Anywhere = RegMask.none
