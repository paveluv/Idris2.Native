-- The allocation check (`Native.Codegen.AllocCheck`) on located IR
-- written by hand: a function it accepts, and one for each defect it must
-- reject. Register allocation never makes these: the check reads what an
-- allocator made without trusting it, so its rejections are shown on code
-- made wrong on purpose.
--
-- Each function is a few blocks of the located IR, every value in a slot
-- of its own (`slotN:T`). The accepted one is as the Idris
--
--     keep : a -> List a
--     keep x = [x]            -- allocates a cons cell, x live across
--
-- written with its live list right; each defect then breaks one rule:
--
-- * a slot read before anything writes it;
-- * a slot written as a `Val` and read as a `W64`, which would hide a value
--   from the collector;
-- * an allocation whose live list leaves out a `Val` read after it;
-- * a live list naming a slot nothing has written;
-- * a resume block whose parameters are not its continuation's and the
--   result;
-- * a resume block reading a slot its continuation does not keep, which
--   the call does not preserve;
-- * a join reached from two blocks, only one of which writes what it reads.
--
-- A value may also be in a register, named by its index among the target's
-- allocatable ones of its class (on x86-64 word register 0 is rax). One is
-- accepted between two instructions; but no register survives the
-- allocation slow path or a direct call's callee, so a value in one must
-- not be live across either, and a register the target does not describe
-- (index 99) cannot be named.
module Main

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.SortedMap
import Native.Codegen.AllocCheck
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty
import Native.Codegen.LocatedIR.Block
import Native.Codegen.LocatedIR.Cont
import Native.Codegen.LocatedIR.Function
import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Opnd
import Native.Codegen.LocatedIR.Program
import Native.Codegen.LocatedIR.Step
import Native.Codegen.LocatedIR.Terminator
import Native.Codegen.X86.Target
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.Kind
import Native.Types.StringEnc

%default total

TestEnc : Types.Enc.Enc
TestEnc = defaultEnc

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

val : Nat -> Location TestEnc Val
val n = Slot n Val

word : Nat -> Location TestEnc W64
word n = Slot n W64

cons : Nat -> Location TestEnc (PtrTo CON)
cons n = Slot n (PtrTo CON)

||| A CPS function of one parameter, slot 0, from its blocks; block 0 its
||| entry.
fn : String -> List (Block TestEnc) -> Function TestEnc
fn name bs = MkFunction (nm name) CPS [At (val 0)] 0 bs EmptyFC

||| An operation, of no term: the check here reads the located IR alone,
||| so the number of the definition it realises is any.
op : Instr TestEnc -> Step TestEnc
op = Op 0

||| The cons cell of `x` and the empty list, as a `Val`.
cell : (live : List (Place TestEnc)) -> List (Step TestEnc)
cell live =
  [ op (AllocObj (cons 1) (ConH 1 2) [MkArg (R (val 0)), MkArg (Imm {t = Val} 0)] live)
  , op (Widen (val 2) (cons 1)) ]

||| `keep`, right: x is a field, so live across its own allocation.
keep : Function TestEnc
keep = fn "keep" [MkBlock 0 [] (cell [At (val 0)]) (Return (R (val 2)))]

||| A slot read before anything writes it: slot 5.
readUnwritten : Function TestEnc
readUnwritten = fn "readUnwritten" [MkBlock 0 [] [] (Return (R (val 5)))]

||| Slot 3 written as a `Val`, read as a `W64`.
twoKinds : Function TestEnc
twoKinds =
  fn "twoKinds"
    [MkBlock 0 [] [Move (val 3) (val 0), op (Arith Add (word 4) (R (word 3)) (Imm 1))]
       (Return (R (val 0)))]

||| x read after the allocation, its live list empty.
liveLeftOut : Function TestEnc
liveLeftOut =
  fn "liveLeftOut"
    [MkBlock 0 [] (cell []) (TailCall (nm "pair") [MkArg (R (val 2)), MkArg (R (val 0))])]

||| The live list names slot 7, which nothing writes.
listsUnwritten : Function TestEnc
listsUnwritten =
  fn "listsUnwritten" [MkBlock 0 [] (cell [At (val 0), At (val 7)]) (Return (R (val 2)))]

||| A call keeping x, whose resume block takes no x.
resumeShape : Function TestEnc
resumeShape =
  fn "resumeShape"
    [ MkBlock 0 [] [] (Call (nm "f") [] (MkCont 1 [At (val 0)]))
    , MkBlock 1 [At (val 3)] [] (Return (R (val 3))) ]

||| A call keeping nothing, whose resume block reads x.
resumeReads : Function TestEnc
resumeReads =
  fn "resumeReads"
    [ MkBlock 0 [] [] (Call (nm "f") [] (MkCont 1 []))
    , MkBlock 1 [At (val 3)] [] (TailCall (nm "pair") [MkArg (R (val 3)), MkArg (R (val 0))]) ]

||| x moved into a register and returned from it.
inRegister : Function TestEnc
inRegister =
  fn "inRegister" [MkBlock 0 [] [Move (Register 0 Val) (val 0)] (Return (R (Register 0 Val)))]

||| x kept in a register across the allocation of its cell, its live list naming it.
registerAcrossAllocation : Function TestEnc
registerAcrossAllocation =
  fn "registerAcrossAllocation"
    [MkBlock 0 [] (Move (Register 0 Val) (val 0) :: cell [At (val 0), At (Register 0 Val)])
       (TailCall (nm "pair") [MkArg (R (val 2)), MkArg (R (Register 0 Val))])]

||| x kept in a register across a direct call.
registerAcrossCall : Function TestEnc
registerAcrossCall =
  fn "registerAcrossCall"
    [MkBlock 0 [] [ Move (Register 1 Val) (val 0)
                  , op (DirectCall (nm "probe") [] [At (word 3)] False [At (Register 1 Val)]) ]
       (Return (R (Register 1 Val)))]

||| A register past the target's description.
undescribed : Function TestEnc
undescribed =
  fn "undescribed" [MkBlock 0 [] [Move (Register 99 Val) (val 0)] (Return (R (val 0)))]

||| A join, block 3, reading slot 4, which only one of its two
||| predecessors writes.
joinHalf : Function TestEnc
joinHalf =
  fn "joinHalf"
    [ MkBlock 0 [] [op (ValToWord (word 1) (val 0))] (Branch EqR (R (word 1)) (Imm 0) 1 2)
    , MkBlock 1 [] [Move (val 4) (val 0)] (Jump 3)
    , MkBlock 2 [] [] (Jump 3)
    , MkBlock 3 [] [] (Return (R (val 4))) ]

covering
main : IO ()
main = traverse_ one
  [ keep, readUnwritten, twoKinds, liveLeftOut, listsUnwritten, resumeShape, resumeReads, joinHalf
  , inRegister, registerAcrossAllocation, registerAcrossCall, undescribed ]
  where
    covering
    one : Function TestEnc -> IO ()
    one f = putStrLn $ case check (MkProgram x86_64 [f] [] f.name noConIds) of
      Right () => show f.name ++ ": accepted"
      Left why => why
