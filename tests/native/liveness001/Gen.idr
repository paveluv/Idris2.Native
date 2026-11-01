-- What is live in a loop, through a join inside it: the register
-- allocator's liveness, pinned at an allocation, whose live list is what a
-- collection there must keep.
--
-- The function, written by hand in the term IR, is as the Idris
--
--     countDown : a -> a
--     countDown x = go 3
--       where
--         go : Bits64 -> a
--         go 0 = x
--         go i = step (MkInt64 i)    -- a boxed copy of the counter
--           where step : Int64 -> a
--                 step _ = go (i - 1)
--
-- with `go` a loop, a join that jumps back to itself, and `step` a second
-- join inside the loop's body, which the body jumps to and which jumps
-- back to the loop. In the term IR a join is a block with parameters, and
-- a jump passes their values; a variable bound outside a block is read in
-- it directly. The loop's body reads `x` from outside the loop, to return
-- it.
--
-- So `x` is live at the box's allocation: after it, the code goes to
-- `step`, then back to `go`, which may return `x`. The allocator learns
-- what a join's block reads before it lowers the code that jumps there,
-- and `step`'s block reads `x` only through its jump to `go`, whose own
-- set is still being computed when `step`'s is: the allocator completes
-- `step`'s with `go`'s once that is known. Were `x` missing from the
-- allocation's live list, a collection there would not keep it, and would
-- move what it points to from under it.
--
-- The program's located IR is printed: each value in a register of its
-- own, a slot, and each allocation with what is live across it.
module Main

import Core.Name
import Core.Name.Namespace
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Data.SortedSet
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty
import Native.Codegen.LocatedIR.Dump
import Native.Codegen.LocatedIR.Program
import Native.Codegen.RegAlloc
import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Build
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Def
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.Program
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.StaticDef
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var
import Native.Codegen.X86.Target
import Native.Data.Builder
import Native.Data.Distinct
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.Kind
import Native.Types.StringEnc

%default total

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

Loop : Decls Types.Enc.defaultEnc
Loop = MkDecls [MkSig (nm "main") CPS [] False, MkSig (nm "countDown") CPS [Val] False] []

countDownRef : Var (sigs Loop) (MkSig (nm "countDown") CPS [Val] False)
countDownRef = later here

||| The entry, `main = countDown 7`.
mainBody : Closed Loop CPS False []
mainBody = build $ \[] => tailCall countDownRef [Vx {enc = defaultEnc} 7]

||| `countDown x`: the loop `go`, from 3, returns `x` at 0; otherwise it
||| boxes its counter and jumps to `step`, which jumps back to `go` with the
||| counter less one.
countDownBody : Closed Loop CPS False [Val]
countDownBody = build $ \[x] =>
  loop [W64] [W 3] $ \go, [i] => do
    step <- block [Val] $ \[_] => do
      i' <- emit1 (Arith Sub i (W 1))
      go [i']
    leaveIf EqR i (W 0) (return x)
    box <- emit1 (AllocObj Int64H [i])
    boxed <- emit1 (WidenPtr box)
    step [boxed]

covering
main : IO ()
main = do
  let Just m = close mainBody | Nothing => putStrLn "main: a level outside its context"
  let Just c = close countDownBody | Nothing => putStrLn "countDown: a level outside its context"
  -- the names' distinctness decided here, as a producer decides it
  case choose (distinct (map (.name) (sigs Loop)) && distinct (map (.sym) (statics Loop))) of
    Left ok => do
      let program = allocRegs x86_64
                      (MkProgram {d = Loop} [Defined m, Defined c] [] (MkEntry here) noConIds)
      putStr (fastConcat (toList (dumpProgram program)))
    Right _ => putStrLn "names repeat"
