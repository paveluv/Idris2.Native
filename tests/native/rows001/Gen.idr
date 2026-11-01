-- The rendering's check of its own code against the rows
-- (`Native.Codegen.X86.Rows`): of the target's allocatable registers, the
-- code of an instruction may write only its results' and those its row
-- says it clobbers. Register allocation reads the rows, so a value it
-- keeps in any other register is still there after the instruction. A
-- rendering that wrote one would lose that value, so it is refused as it
-- is rendered, a failed compile rather than a wrong program.
--
-- Each function is located IR written by hand, as in allocheck001: every
-- value in a slot of its own (`slotN:T`), or in a register, named by its
-- index among the target's allocatable registers of its class (on x86-64
-- word register 0 is rax, 1 is rcx). Most are the Idris
--
--     answer : a -> Int
--     answer _ = 42
--
-- the 42 made by a constant and returned. x86-64 makes a constant in rax,
-- where the row of a constant wants its result:
--
-- * with the result in rax, the code writes rax, the result's register:
--   rendered;
-- * with the result in a slot, as register allocation leaves every value,
--   the code still makes it in rax, which is neither the result's nor a
--   clobber: refused;
-- * with the result in rcx, the code makes it in rax and moves it to rcx:
--   refused, for rax again.
--
-- And a move of x from its slot into another, which no x86-64 instruction
-- does between two places in memory: refused.
--
-- The slot's constant and the move are then rendered after the local
-- assignment (`Native.Codegen.LocalAssign`), as the code generator renders
-- every function. It puts each operand and result where its row wants it,
-- with moves before and after: the constant into rax, then rax to its
-- slot; x from its slot into rax, then rax to the other. In surface terms
-- nothing changes, the 42 is still returned; the code now writes rax only
-- where rax is a result, and both are rendered.
module Main

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.SortedMap
import Data.SortedSet
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Linkage.Realised
import Native.Codegen.LocalAssign
import Native.Codegen.LocatedIR.Block
import Native.Codegen.LocatedIR.Function
import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Opnd
import Native.Codegen.LocatedIR.Program
import Native.Codegen.LocatedIR.Terminator
import Native.Codegen.RegMask
import Native.Codegen.Target
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Render
import Native.Codegen.X86.Rows
import Native.Codegen.X86.Target
import Native.Intrinsic
import Native.Primitive
import Native.Routine
import Native.Types.Enc
import Native.Types.IntegerRoutine
import Native.Types.StringRoutine

%default total

TestEnc : Types.Enc.Enc
TestEnc = defaultEnc

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

val : Nat -> Location TestEnc Val
val n = Slot n Val

||| A CPS function of one parameter, x in slot 0, of one block.
fn : String -> List (Instr TestEnc) -> Terminator TestEnc -> Function TestEnc
fn name is t = MkFunction (nm name) CPS [At (val 0)] 0 [MkBlock 0 [] is t] EmptyFC

||| 42 made in `d` and returned from it.
answer : String -> Location TestEnc Val -> Function TestEnc
answer name d = fn name [Const d 42] (Return (R d))

inRax, inSlot, inRcx : Function TestEnc
inRax = answer "inRax" (Register 0 Val)
inSlot = answer "inSlot" (val 1)
inRcx = answer "inRcx" (Register 1 Val)

||| x moved from its slot into another, and returned from there.
slotToSlot : Function TestEnc
slotToSlot = fn "slotToSlot" [Move (val 1) (val 0)] (Return (R (val 1)))

||| A contract that realises no routine: these functions call none.
realised : Realised
realised = MkRealised [] Nothing Nothing empty empty empty empty

program : Function TestEnc -> Program TestEnc
program f = MkProgram x86_64 [f] [] f.name noConIds

||| The program's every function rendered in turn, the code itself not
||| kept, or why one is not.
rendered : Program TestEnc -> String
rendered p = either id (const "rendered") $ do
  r <- render TestEnc realised p
  s <- foldlM (\s, f => map fst (r.functionCode s f)) r.first r.functions
  ignore (r.finished s)

covering
main : IO ()
main = do
  let called = callClobbers x86_64
  for_ [inRax, inSlot, inRcx, slotToSlot] $ \f =>
    putStrLn (show f.name ++ ": " ++ rendered (program f))
  for_ [inSlot, slotToSlot] $ \f =>
    putStrLn
      (show f.name ++ ", assigned: "
       ++ rendered (localAssign (row called) (termRow called) cycleTemp (program f)))
