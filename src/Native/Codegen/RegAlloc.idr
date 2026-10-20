||| Register allocation: the term IR (`Native.Codegen.TermIR.Program`) into the
||| located IR (`Native.Codegen.LocatedIR.Program`), spill-everything for now.
|||
||| Every binding gets a `SCRATCH` slot of its own. A value is never
||| redefined, so a variable is the same slot wherever it is in scope, and a
||| slot holds values of one type. The IR names no machine register, so none
||| of the target's reserved ones can occur; an allocator that assigns
||| registers will take them from the target's allocatable ones. A join point
||| becomes a block, and its parameters registers that each jump assigns:
||| every argument first into a fresh register, then into the parameters, so
||| that no argument is overwritten before it is read. A call's continuation
||| becomes a resume block. An immediate where the IR wants a register is
||| materialised just before its use.
|||
||| What is live is computed, not stored. Lowering a body returns, with its
||| code, the registers of its environment it reads, directly or through
||| the blocks it jumps to; so live across an instruction, an allocation or
||| a call is what lowering the code after it returned, in the same pass. A
||| join point's block is the exception: its jumps need its free variables
||| before it is lowered, so `frees` computes them first, once for the whole
||| body, as levels; a jump to the block itself contributes nothing, the
||| least fixed point.
module Native.Codegen.RegAlloc

import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Cont as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Label as LocatedIR
import Native.Codegen.LocatedIR.Mem as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Reg as LocatedIR
import Native.Codegen.LocatedIR.Static as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.Target
import Native.Codegen.TermIR.Body as TermIR
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Def as TermIR
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr as TermIR
import Native.Codegen.TermIR.IsInt as TermIR
import Native.Codegen.TermIR.Mem as TermIR
import Native.Codegen.TermIR.Opnd as TermIR
import Native.Codegen.TermIR.OvOp as TermIR
import Native.Codegen.TermIR.Program as TermIR
import Native.Codegen.TermIR.Sig as TermIR
import Native.Codegen.TermIR.Sizes as TermIR
import Native.Codegen.TermIR.StaticDef as TermIR
import Native.Codegen.TermIR.StaticSig as TermIR
import Native.Codegen.TermIR.Var as TermIR

import Control.Monad.Identity
import Control.Monad.State.Interface
import Control.Monad.State.State
import Core.FC
import Core.Name
import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Data.Zippable
import Native.Data.Builder as Data
import Native.Data.Distinct
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

------------------------------------------------------------------------------
-- Environments

RV : (enc : Types.Enc) -> IRCommon.Ty enc -> Type
RV enc _ = LocatedIR.Reg enc

||| How a variable of the environment is held: in a register, or as the
||| address of a static object, which needs none. A static never moves, so
||| its address is an operand where it is used (`S`), never live across an
||| allocation and never in a slot. The term binds one by `StaticAddr` and
||| widens it to a value by `WidenPtr`; the environment holds both as the
||| static.
data Held : Types.Enc -> Type where
  InReg : LocatedIR.Reg enc -> Held enc
  OfStatic : Name -> Held enc

HV : (enc : Types.Enc) -> IRCommon.Ty enc -> Type
HV enc _ = Held enc

||| Registers, by identity.
RegMap : Types.Enc -> Type
RegMap enc = SortedMap Nat (LocatedIR.Reg enc)

record LabelInfo (enc : Types.Enc) where
  constructor MkLabelInfo
  label : LocatedIR.Label
  params : List (LocatedIR.Reg enc)
  ||| The registers the block reads from outside it, its parameters excluded.
  free : RegMap enc

LI : (enc : Types.Enc) -> List (IRCommon.Ty enc) -> Type
LI enc _ = LabelInfo enc

append : All p xs -> All p ys -> All p (xs ++ ys)
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

regs : All (RV enc) ts -> List (LocatedIR.Reg enc)
regs [] = []
regs (r :: rs) = r :: regs rs

||| Registers, as the environment holds them.
held : All (RV enc) ts -> All (HV enc) ts
held [] = []
held (r :: rs) = InReg r :: held rs

without : List (LocatedIR.Reg enc) -> RegMap enc -> RegMap enc
without ds m = foldr (\d => delete (LocatedIR.Reg.slot d)) m ds

------------------------------------------------------------------------------
-- Free variables

one : Held enc -> RegMap enc
one (InReg r) = singleton (LocatedIR.Reg.slot r) r
one (OfStatic _) = empty

uses : All (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t -> RegMap enc
uses env (TermIR.Opnd.V x) = one (TermIR.Var.fetch x env)
uses _ _ = empty

usesAll : All (HV enc) ctx -> All (TermIR.Opnd (TermIR.Var ctx)) ts -> RegMap enc
usesAll env [] = empty
usesAll env (x :: xs) = mergeLeft (uses env x) (usesAll env xs)

------------------------------------------------------------------------------
-- The free variables of join blocks

||| A variable as its level: its position from the bottom of its context,
||| which does not change as the context grows.
Level : Type
Level = Nat

||| What a join's block reads from outside: the depth of the join's context
||| and the levels below it, which the lowering of the join turns into the
||| registers of its environment.
JoinFrees : Type
JoinFrees = (Nat, SortedSet Level)

------------------------------------------------------------------------------
-- The conversion's state

record St (enc : Types.Enc) where
  constructor MkSt
  nextReg : Nat
  nextLabel : Nat
  ||| The blocks made so far, by label. Labels are taken in reading order.
  blocks : SortedMap LocatedIR.Label (LocatedIR.Block enc)
  ||| What the blocks of the joins still to be lowered read, in the order
  ||| the lowering meets them (`frees`).
  joins : List JoinFrees

M : Types.Enc -> Type -> Type
M enc = State (St enc)

fresh : IRCommon.Ty enc -> M enc (LocatedIR.Reg enc)
fresh t = do
  s <- get
  put ({ nextReg := S s.nextReg } s)
  pure (LocatedIR.Reg.Slot s.nextReg t)

freshAll : (ts : List (IRCommon.Ty enc)) -> M enc (All (RV enc) ts)
freshAll [] = pure []
freshAll (t :: ts) = [| fresh t :: freshAll ts |]

freshLabel : M enc LocatedIR.Label
freshLabel = do
  s <- get
  put ({ nextLabel := S s.nextLabel } s)
  pure s.nextLabel

||| A block's code: its instructions, as the lowering produces them, and
||| its terminator.
Code : Types.Enc -> Type
Code enc = (Data.Builder (LocatedIR.Instr enc), LocatedIR.Terminator enc)

addBlock : LocatedIR.Label -> List (LocatedIR.Reg enc) -> Code enc -> M enc ()
addBlock l ps (is, t) = modify { blocks $= insert l (LocatedIR.MkBlock l ps (toList is) t) }

||| Code, with the registers of its environment it reads.
Lowered : Types.Enc -> Type
Lowered enc = (RegMap enc, Code enc)

------------------------------------------------------------------------------
-- Operands

operand : All (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t -> LocatedIR.Opnd enc
operand env (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
  InReg r => LocatedIR.Opnd.R r
  OfStatic s => LocatedIR.Opnd.StaticRef s
operand env (TermIR.Opnd.W i) = LocatedIR.Opnd.Imm i
operand env (TermIR.Opnd.Fx i) = LocatedIR.Opnd.Imm i
operand env (TermIR.Opnd.Vx i) = LocatedIR.Opnd.Imm i
operand env TermIR.Opnd.Erased = LocatedIR.Opnd.Imm 0

operands : All (HV enc) ctx -> All (TermIR.Opnd (TermIR.Var ctx)) ts -> List (LocatedIR.Opnd enc)
operands env [] = []
operands env (x :: xs) = operand env x :: operands env xs

||| An operand in a register, with the instruction that materialises an
||| immediate.
asReg : All (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t ->
        M enc (List (LocatedIR.Instr enc), LocatedIR.Reg enc)
asReg env (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
  InReg r => pure ([], r)
  OfStatic s => do r <- fresh IRCommon.Ty.Val; pure ([LocatedIR.Instr.StaticAddr r s], r)
asReg env (TermIR.Opnd.W i) = do r <- fresh IRCommon.Ty.W64; pure ([LocatedIR.Instr.Const r i], r)
asReg env (TermIR.Opnd.Fx {fx} i) = do r <- fresh IRCommon.Ty.Fix
                                       pure ([LocatedIR.Instr.Const r i], r)
asReg env (TermIR.Opnd.Vx {fx} i) = do r <- fresh IRCommon.Ty.Val
                                       pure ([LocatedIR.Instr.Const r i], r)
asReg env TermIR.Opnd.Erased = do r <- fresh IRCommon.Ty.Val; pure ([LocatedIR.Instr.Const r 0], r)

------------------------------------------------------------------------------
-- Instructions and bodies

parameters (d : TermIR.Decls enc)
  varName : TermIR.Var d.sigs s -> Name
  varName r = (TermIR.Var.entry d.sigs r).name

  varSym : TermIR.Var d.statics s -> Name
  varSym r = (TermIR.Var.entry d.statics r).sym

  mutual
    ||| Where a branch goes: a block of the body's own, or, when the body only
    ||| jumps to a block without parameters, that block.
    branchTo : TermIR.Body d c m ls ctx -> All (HV enc) ctx -> All (LI enc) ls ->
               M enc (RegMap enc, LocatedIR.Label)
    branchTo (TermIR.Body.Jump l []) env li = let info =
                                                    TermIR.Var.fetch l li in pure
                                                      (info.free, info.label)
    branchTo b env li = do
      lb <- freshLabel
      (fb, code) <- body b env li
      addBlock lb [] code
      pure (fb, lb)

    ||| The code of a body, and the registers of its environment it reads.
    ||| Labels are taken before the code under them is lowered, so that they
    ||| number the blocks in reading order.
    body : TermIR.Body d c m ls ctx -> All (HV enc) ctx -> All (LI enc) ls -> M enc (Lowered enc)
    -- a static's address is held as itself, and so is the value it widens to
    body (TermIR.Body.Bind (TermIR.Instr.StaticAddr s) k) env li =
      body k (OfStatic (varSym s) :: env) li
    body (TermIR.Body.Bind (TermIR.Instr.WidenPtr (TermIR.Opnd.V x)) k) env li =
      case TermIR.Var.fetch x env of
      OfStatic s => body k (OfStatic s :: env) li
      InReg _ => bind [IRCommon.Ty.Val] (TermIR.Instr.WidenPtr (TermIR.Opnd.V x)) k env li
    body (TermIR.Body.Bind {ts} i k) env li = bind ts i k env li
    body (TermIR.Body.Join ps b r) env li = do
      l <- freshLabel
      params <- freshAll ps
      (depth, levels) <- popJoin
      let fb = registersAt env depth levels
          info = MkLabelInfo l (regs params) fb
      (fr, codeR) <- body r env (info :: li)
      (_, codeB) <- body b (append (held params) env) (info :: li)
      addBlock l [] codeB
      pure (fr, codeR)
      where
        ||| What the next join's block reads.
        popJoin : M enc JoinFrees
        popJoin = do
          s <- get
          case s.joins of
            j :: js => do put ({ joins := js } s); pure j
            [] => pure (0, empty)

        ||| The registers of the environment, `depth` deep, at the levels.
        registersAt : All (HV enc) ctx -> (depth : Nat) -> SortedSet Level -> RegMap enc
        registersAt env depth lvs = foldl add empty (Prelude.toList lvs)
          where
            at : Nat -> All (HV enc) xs -> Maybe (Held enc)
            at _ [] = Nothing
            at Z (h :: _) = Just h
            at (S i) (_ :: hs) = at i hs

            add : RegMap enc -> Level -> RegMap enc
            add m l = case at (minus depth (S l)) env of
              Just (InReg r) => insert (LocatedIR.Reg.slot r) r m
              _ => m
    body (TermIR.Body.Jump l xs) env li = do
      let info = TermIR.Var.fetch l li
      code <- jump env info xs
      pure (mergeLeft info.free (usesAll env xs), code)
      where
        ||| A jump to a block: the arguments into its parameters. When an argument
        ||| reads one of those parameters, every argument goes into a fresh
        ||| register first, so that none is overwritten before it is read.
        jump : All (HV enc) ctx -> LabelInfo enc -> All (TermIR.Opnd (TermIR.Var ctx)) ps ->
               M enc (Code enc)
        jump env info xs =
          if any (\r => isJust (lookup (LocatedIR.Reg.slot r) (usesAll env xs))) info.params
             then do
               (loads, temps) <- moves info.params xs
               pure (Data.Builder.piece (loads ++ zipWith LocatedIR.Instr.Move info.params temps),
                     LocatedIR.Terminator.Jump info.label)
             else pure
               (Data.Builder.piece (direct info.params xs), LocatedIR.Terminator.Jump info.label)
          where
            ||| An operand into a given register.
            moveInto : All (HV enc) ctx -> LocatedIR.Reg enc -> TermIR.Opnd (TermIR.Var ctx) t ->
                       LocatedIR.Instr enc
            moveInto env d (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
              InReg r => LocatedIR.Instr.Move d r
              OfStatic s => LocatedIR.Instr.StaticAddr d s
            moveInto env d (TermIR.Opnd.W i) = LocatedIR.Instr.Const d i
            moveInto env d (TermIR.Opnd.Fx i) = LocatedIR.Instr.Const d i
            moveInto env d (TermIR.Opnd.Vx i) = LocatedIR.Instr.Const d i
            moveInto env d TermIR.Opnd.Erased = LocatedIR.Instr.Const d 0

            direct : List (LocatedIR.Reg enc) -> All (TermIR.Opnd (TermIR.Var ctx)) qs ->
                     List (LocatedIR.Instr enc)
            direct (p :: ps) (x :: xs) = moveInto env p x :: direct ps xs
            direct _ _ = []

            moves : List (LocatedIR.Reg enc) -> All (TermIR.Opnd (TermIR.Var ctx)) qs ->
                    M enc (List (LocatedIR.Instr enc), List (LocatedIR.Reg enc))
            moves (p :: ps) (x :: xs) = do
              t <- fresh (LocatedIR.Reg.ty p)
              (is, ts) <- moves ps xs
              pure (moveInto env t x :: is, t :: ts)
            moves _ _ = pure ([], [])
    body (TermIR.Body.Branch rel x y a b) env li = do
      (fa, la) <- branchTo a env li
      (fb, lb) <- branchTo b env li
      pure (mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft fa fb),
            (neutral, LocatedIR.Terminator.Branch rel (operand env x) (operand env y) la lb))
    body (TermIR.Body.IfFixnums {fx} vs y no) env li = do
      ly <- freshLabel
      loaded <- traverse (asReg env) vs
      let rs = map snd loaded
      (narrows, fs) <- narrowAll rs
      (fy, (isY, tY)) <- body y (append (held fs) env) li
      addBlock ly [] (Data.Builder.piece narrows <+> isY, tY)
      (fn, ln) <- branchTo no env li
      pure (mergeLeft (usesVect env vs) (mergeLeft (without (regs fs) fy) fn),
            (concatMap (Data.Builder.piece . fst) (toList loaded),
              LocatedIR.Terminator.IfFixnums (toList rs) ly ln))
      where
        usesVect : All (HV enc) ctx -> Vect n (TermIR.Opnd (TermIR.Var ctx) t) -> RegMap enc
        usesVect env = foldr (\x, m => mergeLeft (uses env x) m) empty

        narrowAll : Vect n (LocatedIR.Reg enc) ->
                    M enc (List (LocatedIR.Instr enc),
                           All (RV enc) (replicate n (IRCommon.Ty.Fix {enc})))
        narrowAll [] = pure ([], [])
        narrowAll (r :: rs) = do
          f <- fresh IRCommon.Ty.Fix
          (is, fs) <- narrowAll rs
          pure (LocatedIR.Instr.Narrow IRCommon.Ty.Fix f r :: is, f :: fs)
    body (TermIR.Body.ArithOv {t} o x y ok ovf) env li = do
      f <- fresh t
      (fok, (isOk, tOk)) <- body ok (InReg f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft (without [f] fok) fov),
            (Data.Builder.single
              (LocatedIR.Instr.ArithOv (TermIR.OvOp.ovArith o) f (operand env x) (operand env y) lo)
              <+> isOk, tOk))
    body (TermIR.Body.TagOv {fx} x ok ovf) env li = do
      (px, rx) <- asReg env x
      f <- fresh IRCommon.Ty.Fix
      (fok, (isOk, tOk)) <- body ok (InReg f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (uses env x) (mergeLeft (without [f] fok) fov),
            (Data.Builder.piece (px ++ [LocatedIR.Instr.TagOv f rx lo]) <+> isOk, tOk))
    body (TermIR.Body.Switch x keys bs dflt) env li = do
      (px, rx) <- asReg env x
      (fcs, labels) <- cases bs env li
      (fd, ld) <- branchTo dflt env li
      pure (mergeLeft (uses env x) (mergeLeft fcs fd),
            (Data.Builder.piece px, LocatedIR.Terminator.Switch rx (zip keys labels) ld))
      where
        ||| A switch's cases, each a block of its own, in order.
        cases : All (\_ => TermIR.Body d c m ls ctx) ks -> All (HV enc) ctx -> All (LI enc) ls ->
                M enc (RegMap enc, List LocatedIR.Label)
        cases [] env li = pure (empty, [])
        cases (b :: bs) env li = do
          (fb, l) <- branchTo b env li
          (fbs, ls) <- cases bs env li
          pure (mergeLeft fb fbs, l :: ls)
    body (TermIR.Body.Call f xs k) env li = do
      lr <- freshLabel
      r <- fresh IRCommon.Ty.Val
      (fk, codeK) <- body k (InReg r :: env) li
      let outer = without [r] fk
          live = values outer
      addBlock lr (live ++ [r]) codeK
      pure (mergeLeft (usesAll env xs) outer,
            (neutral,
              LocatedIR.Terminator.Call (varName f) (operands env xs) (LocatedIR.MkCont lr live)))
    body (TermIR.Body.TailCall f xs) env li =
      pure (usesAll env xs, (neutral, LocatedIR.Terminator.TailCall (varName f) (operands env xs)))
    body (TermIR.Body.Apply f x k) env li = do
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      lr <- freshLabel
      r <- fresh IRCommon.Ty.Val
      (fk, codeK) <- body k (InReg r :: env) li
      let outer = without [r] fk
          live = values outer
      addBlock lr (live ++ [r]) codeK
      pure (mergeLeft (mergeLeft (uses env f) (uses env x)) outer,
            (Data.Builder.piece (pf ++ px),
              LocatedIR.Terminator.Apply rf rx (LocatedIR.MkCont lr live)))
    body (TermIR.Body.TailApply f x) env li = do
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      pure (mergeLeft (uses env f) (uses env x),
            (Data.Builder.piece (pf ++ px), LocatedIR.Terminator.TailApply rf rx))
    body (TermIR.Body.Return x) env li =
      pure (uses env x, (neutral, LocatedIR.Terminator.Return (operand env x)))
    body (TermIR.Body.Enter f xs) env li = do
      (pf, rf) <- asReg env f
      pure (mergeLeft (uses env f) (usesList env xs),
            (Data.Builder.piece pf, LocatedIR.Terminator.Enter rf (map (operand env) xs)))
      where
        usesList : All (HV enc) ctx -> List (TermIR.Opnd (TermIR.Var ctx) t) -> RegMap enc
        usesList env = foldr (\x, m => mergeLeft (uses env x) m) empty
    body (TermIR.Body.Ret xs) env li =
      pure (usesAll env xs, (neutral, LocatedIR.Terminator.Ret (operands env xs)))
    body (TermIR.Body.Crash s) env li = pure (empty, (neutral, LocatedIR.Terminator.Crash s))
    body (TermIR.Body.Unsupported s) env li =
      pure (empty, (neutral, LocatedIR.Terminator.Unsupported s))

    ||| An instruction's registers, bound in the environment of the rest.
    bind : (ts : List (IRCommon.Ty enc)) -> TermIR.Instr d m (TermIR.Var ctx) ts ->
           TermIR.Body d c m ls (ts ++ ctx) ->
           All (HV enc) ctx -> All (LI enc) ls -> M enc (Lowered enc)
    bind ts i k env li = do
      ds <- freshAll ts
      (after, (is, t)) <- body k (append (held ds) env) li
      let outer = without (regs ds) after
      pre <- instr env ds outer i
      pure (mergeLeft (instrUses env i) outer, (Data.Builder.piece pre <+> is, t))
      where
        ||| The registers of the environment an instruction reads.
        instrUses : All (HV enc) ctx -> TermIR.Instr d m (TermIR.Var ctx) ts -> RegMap enc
        instrUses env i = execState empty (TermIR.Instr.traverseInstr (collect env) i)
          where
            collect : All (HV enc) ctx -> {0 t : IRCommon.Ty enc} ->
                      TermIR.Opnd (TermIR.Var ctx) t ->
                      State (RegMap enc) (TermIR.Opnd (TermIR.Var ctx) t)
            collect env x = do modify (mergeLeft (uses env x)); pure x

        ||| The IR of an instruction binding the registers `ds`, given what is live
        ||| after it.
        instr : All (HV enc) ctx''' -> All (RV enc) ts' -> (after : RegMap enc) ->
                TermIR.Instr d m' (TermIR.Var ctx''') ts' ->
                M enc (List (LocatedIR.Instr enc))
        instr env z after instr' = case (z, instr') of
          ([r], TermIR.Instr.FConst x) => pure [LocatedIR.Instr.FConst r x]
          ([r], TermIR.Instr.CodeAddr f) => pure [LocatedIR.Instr.CodeAddr r (varName f)]
          -- not reached: `body` holds a static's address as itself, in no register
          ([r], TermIR.Instr.StaticAddr s) => pure [LocatedIR.Instr.StaticAddr r (varSym s)]
          ([r], TermIR.Instr.AreaAddr a) => pure [LocatedIR.Instr.AreaAddr r a]
          ([r], TermIR.Instr.TableAddr n) => pure [LocatedIR.Instr.TableAddr r n]
          ([r], TermIR.Instr.Arith o x y) =>
            pure [LocatedIR.Instr.Arith o r (operand env x) (operand env y)]
          ([h, l], TermIR.Instr.Mul128 x y) =>
            pure [LocatedIR.Instr.Mul128 h l (operand env x) (operand env y)]
          ([r], TermIR.Instr.Unary o x) => unary env x (LocatedIR.Instr.Unary o r)
          ([r], TermIR.Instr.Ext w s x) => unary env x (LocatedIR.Instr.Ext w s r)
          ([r], TermIR.Instr.FArith o x y) => binary env x y (LocatedIR.Instr.FArith o r)
          ([r], TermIR.Instr.FNeg x) => unary env x (LocatedIR.Instr.FNeg r)
          ([r], TermIR.Instr.FCmp rel x y) => binary env x y (LocatedIR.Instr.FCmp rel r)
          ([r], TermIR.Instr.Convert op x) => unary env x (LocatedIR.Instr.Convert op r)
          ([r], TermIR.Instr.Cmp rel x y) =>
            pure [LocatedIR.Instr.Cmp rel r (operand env x) (operand env y)]
          ([r], TermIR.Instr.Load t mem) => do (p, m') <- memRef env mem
                                               pure (p ++ [LocatedIR.Instr.Load t r m'])
          ([], TermIR.Instr.Store t mem x) => do
            (p, m') <- memRef env mem
            (px, rx) <- asReg env x
            pure (p ++ px ++ [LocatedIR.Instr.Store t m' rx])
          ([r], TermIR.Instr.LoadN w s mem) => do (p, m') <- memRef env mem
                                                  pure (p ++ [LocatedIR.Instr.LoadN w s r m'])
          ([], TermIR.Instr.StoreN w mem x) => do
            (p, m') <- memRef env mem
            (px, rx) <- asReg env x
            pure (p ++ px ++ [LocatedIR.Instr.StoreN w m' rx])
          ([r], TermIR.Instr.Tag {fx} x) => unary env x (LocatedIR.Instr.Tag r)
          ([r], TermIR.Instr.Untag {fx} x) => unary env x (LocatedIR.Instr.Untag r)
          ([r], TermIR.Instr.NarrowFix {fx} x) =>
            unary env x (LocatedIR.Instr.Narrow IRCommon.Ty.Fix r)
          ([r], TermIR.Instr.NarrowPtr k x) =>
            unary env x (LocatedIR.Instr.Narrow (IRCommon.Ty.PtrTo k) r)
          ([r], TermIR.Instr.WidenFix x) => unary env x (LocatedIR.Instr.Widen r)
          ([r], TermIR.Instr.WidenPtr x) => unary env x (LocatedIR.Instr.Widen r)
          ([r], TermIR.Instr.AddrToWord x) => unary env x (LocatedIR.Instr.AddrToWord r)
          ([r], TermIR.Instr.WordToAddr k x) => unary env x (LocatedIR.Instr.WordToAddr k r)
          ([r], TermIR.Instr.ValToWord x) => unary env x (LocatedIR.Instr.ValToWord r)
          ([r], TermIR.Instr.WordToVal x) => unary env x (LocatedIR.Instr.WordToVal r)
          ([r], TermIR.Instr.LoadHeader x) => unary env x (LocatedIR.Instr.LoadHeader r)
          ([r], TermIR.Instr.LoadPart p x) => unary env x (LocatedIR.Instr.LoadPart p r)
          ([r], TermIR.Instr.AllocObj h fs) =>
            -- the fields are written after the slow path's collection
            let live = values (mergeLeft after (usesAll env fs))
            in pure [LocatedIR.Instr.AllocObj r h (operands env fs) live]
          ([r], TermIR.Instr.AllocSized p n f) => do
            (pn, rn) <- asReg env n
            let fill = fillOperand p f
                live =
                  values
                    (mergeLeft after
                     (mergeLeft (one (InReg rn)) (maybe empty (fillUses p f) (Just ()))))
            pure (pn ++ [LocatedIR.Instr.AllocSized r p rn fill live])
          (ds, TermIR.Instr.DirectCall f xs) =>
            pure
              [LocatedIR.Instr.DirectCall (varName f) (operands env xs) (regs ds) (isCollecting f)
               (values after)]
          ([d], TermIR.Instr.GetPinned r) => pure [LocatedIR.Instr.GetPinned r d]
          ([], TermIR.Instr.SetPinned r x) => pure [LocatedIR.Instr.SetPinned r (operand env x)]
          ([d], TermIR.Instr.SystemCall _ xs) =>
            pure [LocatedIR.Instr.SystemCall d (operands env xs)]
          ([], TermIR.Instr.Loc fc) => pure [LocatedIR.Instr.Loc fc]
          ([], TermIR.Instr.Comment s) => pure [LocatedIR.Instr.Comment s]
          where
            fillOperand : {0 kind : Types.Kind} -> (q : Types.Header.HeaderPart kind) ->
                          TermIR.Sizes.Fill (TermIR.Var ctx''') q -> Maybe (LocatedIR.Opnd enc)
            fillOperand Types.Header.ArrayElems x = Just (operand env x)
            fillOperand _ _ = Nothing
            fillUses : {0 kind : Types.Kind} -> (q : Types.Header.HeaderPart kind) ->
                       TermIR.Sizes.Fill (TermIR.Var ctx''') q -> () -> RegMap enc
            fillUses Types.Header.ArrayElems x _ = uses env x
            fillUses _ _ _ = empty

            isCollecting : TermIR.Var d.sigs s -> Bool
            isCollecting r = case (TermIR.Var.entry d.sigs r).conv of
              IRCommon.Conv.CPS => False
              IRCommon.Conv.Direct _ col => col

            memRef : All (HV enc'') ctx'' -> TermIR.Mem (TermIR.Var ctx'') ->
                     M enc'' (List (LocatedIR.Instr enc''), LocatedIR.Mem enc'')
            memRef env (TermIR.MkMem b i o) = do
              (pb, rb) <- baseReg env b
              case i of
                Nothing => pure (pb, LocatedIR.MkMem rb Nothing o)
                Just x => do (pi, ri) <- asReg env x
                             pure (pb ++ pi, LocatedIR.MkMem rb (Just ri) o)
              where
                baseReg : All (HV enc') ctx' -> TermIR.Mem.Base (TermIR.Var ctx') ->
                          M enc' (List (LocatedIR.Instr enc'), LocatedIR.Reg enc')
                baseReg env (TermIR.Mem.AtWord x) = asReg env x
                baseReg env (TermIR.Mem.AtPtr x) = asReg env x

            ||| One register, through an instruction that reads it from an operand.
            unary : All (HV enc) ctx' -> TermIR.Opnd (TermIR.Var ctx') t ->
                    (LocatedIR.Reg enc -> LocatedIR.Instr enc) -> M enc (List (LocatedIR.Instr enc))
            unary env x f = do (p, r) <- asReg env x; pure (p ++ [f r])

            binary : All (HV enc) ctx' -> TermIR.Opnd (TermIR.Var ctx') t ->
                     TermIR.Opnd (TermIR.Var ctx') u ->
                     (LocatedIR.Reg enc -> LocatedIR.Reg enc -> LocatedIR.Instr enc) ->
                     M enc (List (LocatedIR.Instr enc))
            binary env x y f = do (px, rx) <- asReg env x
                                  (py, ry) <- asReg env y
                                  pure (px ++ py ++ [f rx ry])

  functions : (ss : List (TermIR.Sig enc)) -> All (TermIR.Def d) ss -> List (LocatedIR.Function enc)
  functions [] [] = []
  functions (s :: ss) (TermIR.Def.Defined b :: ds) = function s b :: functions ss ds
    where
      function : (s : TermIR.Sig enc) -> TermIR.Body d s.conv s.converts [] s.params ->
                 LocatedIR.Function enc
      function s b =
        let run : M enc (List (LocatedIR.Reg enc))
            run = do
              ps <- freshAll s.params
              modify { joins := snd (frees b (length s.params) []) [] }
              (_, code) <- body b (held ps) []
              addBlock 0 [] code
              pure (regs ps)
        in case runState (MkSt 0 1 empty []) run of
             (st, ps) => LocatedIR.MkFunction s.name s.conv ps 0 (values st.blocks) EmptyFC
        where
          ||| The levels a body reads of the variables bound outside it, directly or
          ||| through the blocks it jumps to (`lf` is what each label in scope reads);
          ||| and what each join's block reads, in the order the lowering meets the
          ||| joins: a join, then those in the code that reaches it, then those in
          ||| its block. Once for a whole body: computing a block's at its join read
          ||| the rest of the function again at every join, the square of its length.
          frees : TermIR.Body d'' c m ls ctx -> (depth : Nat) -> All (\_ => SortedSet Level) ls ->
                  (SortedSet Level, List JoinFrees -> List JoinFrees)
          frees body' depth lf = case body' of
            TermIR.Body.Bind {ts} i k =>
                          let (fk, jk) = frees k (depth + length ts) lf
                          in (union (instrLevels depth i) (outside depth (length ts) fk), jk)
            TermIR.Body.Join ps b r =>
                          let (fb, jb) = frees b (depth + length ps) (empty :: lf)
                              block = outside depth (length ps) fb
                              (fr, jr) = frees r depth (block :: lf)
                          in (fr, \rest => (depth, block) :: jr (jb rest))
            TermIR.Body.Jump l xs => (union (TermIR.Var.fetch l lf) (opsLevels depth xs), id)
            TermIR.Body.Branch _ x y a b =>
              let (fa, ja) = frees a depth lf
                  (fb, jb) = frees b depth lf
              in (union (union (opLevel depth x) (opLevel depth y)) (union fa fb), ja . jb)
            TermIR.Body.IfFixnums {n} vs y no =>
              let (fy, jy) = frees y (depth + S n) lf
                  (fn, jn) = frees no depth lf
              in (union (vectLevels depth vs) (union (outside depth (S n) fy) fn), jy . jn)
            TermIR.Body.ArithOv _ x y ok ovf =>
              let (fo, jo) = frees ok (S depth) lf
                  (fv, jv) = frees ovf depth lf
              in (union (union (opLevel depth x) (opLevel depth y)) (union (outside depth 1 fo) fv),
                  jo . jv)
            TermIR.Body.TagOv x ok ovf =>
              let (fo, jo) = frees ok (S depth) lf
                  (fv, jv) = frees ovf depth lf
              in (union (opLevel depth x) (union (outside depth 1 fo) fv), jo . jv)
            TermIR.Body.Switch x _ bs dflt =>
              let (fc, jc) = freesCases bs depth lf
                  (fd, jd) = frees dflt depth lf
              in (union (opLevel depth x) (union fc fd), jc . jd)
            TermIR.Body.Call _ xs k =>
              let (fk, jk) =
                    frees k (S depth) lf in (union (opsLevels depth xs) (outside depth 1 fk), jk)
            TermIR.Body.TailCall _ xs => (opsLevels depth xs, id)
            TermIR.Body.Apply f x k =>
              let (fk, jk) = frees k (S depth) lf
              in (union (union (opLevel depth f) (opLevel depth x)) (outside depth 1 fk), jk)
            TermIR.Body.TailApply f x => (union (opLevel depth f) (opLevel depth x), id)
            TermIR.Body.Return x => (opLevel depth x, id)
            TermIR.Body.Enter f xs => (union (opLevel depth f) (listLevels depth xs), id)
            TermIR.Body.Ret xs => (opsLevels depth xs, id)
            TermIR.Body.Crash _ => (empty, id)
            TermIR.Body.Unsupported _ => (empty, id)
            where
              opLevel : (depth : Nat) -> TermIR.Opnd (TermIR.Var ctx'') t -> SortedSet Level
              opLevel depth (TermIR.Opnd.V x) = singleton (level depth x)
                where
                  ||| The level of a variable in a context of `depth` entries.
                  level : (depth : Nat) -> TermIR.Var ctx' t' -> Level
                  level depth v = minus depth (S v.index)
              opLevel _ _ = empty

              ||| The levels an instruction reads.
              instrLevels : (depth : Nat) -> TermIR.Instr d' m' (TermIR.Var ctx') ts' ->
                            SortedSet Level
              instrLevels depth i =
                execState empty
                  (TermIR.Instr.traverseInstr (\x => do modify (union (opLevel depth x)); pure x) i)

              vectLevels : (depth : Nat) -> Vect n' (TermIR.Opnd (TermIR.Var ctx) t) ->
                           SortedSet Level
              vectLevels depth = foldr (union . opLevel depth) empty

              freesCases : All (\_ => TermIR.Body d' c' m' ls' ctx') ks -> (depth : Nat) ->
                           All (\_ => SortedSet Level) ls' ->
                           (SortedSet Level, List JoinFrees -> List JoinFrees)
              freesCases [] depth lf = (empty, id)
              freesCases (b :: bs) depth lf =
                let (fb, jb) = frees b depth lf
                    (fs, js) = freesCases bs depth lf
                in (union fb fs, jb . js)

              listLevels : (depth : Nat) -> List (TermIR.Opnd (TermIR.Var ctx) t) -> SortedSet Level
              listLevels depth = foldr (union . opLevel depth) empty

              opsLevels : (depth : Nat) -> All (TermIR.Opnd (TermIR.Var ctx)) ts -> SortedSet Level
              opsLevels depth [] = empty
              opsLevels depth (x :: xs) = union (opLevel depth x) (opsLevels depth xs)

              ||| The levels of a body's own first `n` binders, from `depth`, taken out of
              ||| what it reads: what is left, it reads from outside.
              outside : (depth : Nat) -> (n : Nat) -> SortedSet Level -> SortedSet Level
              outside depth Z s = s
              outside depth (S n) s = outside (S depth) n (delete depth s)
  functions (_ :: ss) (TermIR.Def.External :: ds) = functions ss ds

  statics : (ss : List TermIR.StaticSig) -> All (TermIR.StaticDef d) ss ->
            List (LocatedIR.Static enc)
  statics [] [] = []
  statics (TermIR.MkStaticSig sym k :: ss) (TermIR.MkStaticDef h fs :: ds) =
    LocatedIR.MkStatic sym k h (map field (toList fs)) :: statics ss ds
    where
      field : TermIR.StaticDef.SField d -> LocatedIR.Static.SField
      field (TermIR.StaticDef.SWord w) = LocatedIR.Static.SWord w
      field (TermIR.StaticDef.SRef s) = LocatedIR.Static.SRef (varSym s)
      field (TermIR.StaticDef.SCode f) = LocatedIR.Static.SCode (varName f)

  entryName : TermIR.Program.Entry d -> Name
  entryName (TermIR.Program.MkEntry f) = varName f

||| The IR's programs, for producers that build terms and need not import
||| the IR, whose names the term's share.
export
0 LocatedProgram : Types.Enc -> Type
LocatedProgram enc = LocatedIR.Program enc

||| The program in the IR, for the target.
export
allocRegs : {d : TermIR.Decls enc} -> Target -> TermIR.Program enc d -> LocatedIR.Program enc
allocRegs target (TermIR.MkProgram fs ss e conIds) =
  LocatedIR.MkProgram target (functions d d.sigs fs) (statics d d.statics ss) (entryName d e) conIds
