||| Register allocation: the term IR (`Compiler.Native.TermIR`) into the
||| located IR (`Compiler.Native.LocatedIR`), spill-everything for now.
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
module Compiler.Native.RegAlloc

import Compiler.Native.TermIR
import Compiler.Native.LocatedIR
import Compiler.Native.Target
import Control.Monad.State
import Data.SortedMap
import Data.SortedSet

%default total

------------------------------------------------------------------------------
-- Environments

R : Enc -> Type
R enc = Reg enc

RV : (enc : Enc) -> Ty enc -> Type
RV enc _ = R enc

||| How a variable of the environment is held: in a register, or as the
||| address of a static object, which needs none. A static never moves, so
||| its address is an operand where it is used (`S`), never live across an
||| allocation and never in a slot. The term binds one by `StaticAddr` and
||| widens it to a value by `WidenPtr`; the environment holds both as the
||| static.
data Held : Enc -> Type where
  InReg : Reg enc -> Held enc
  OfStatic : Name -> Held enc

HV : (enc : Enc) -> Ty enc -> Type
HV enc _ = Held enc

||| Registers, by identity.
RegMap : Enc -> Type
RegMap enc = SortedMap Nat (R enc)

record LabelInfo (enc : Enc) where
  constructor MkLabelInfo
  label : BlockLabel
  params : List (R enc)
  ||| The registers the block reads from outside it, its parameters excluded.
  free : RegMap enc

LI : (enc : Enc) -> List (Ty enc) -> Type
LI enc _ = LabelInfo enc

append : All p xs -> All p ys -> All p (xs ++ ys)
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

regs : All (RV enc) ts -> List (R enc)
regs [] = []
regs (r :: rs) = r :: regs rs

||| Registers, as the environment holds them.
held : All (RV enc) ts -> All (HV enc) ts
held [] = []
held (r :: rs) = InReg r :: held rs

without : List (R enc) -> RegMap enc -> RegMap enc
without ds m = foldr (\d => delete (slotOf d)) m ds

------------------------------------------------------------------------------
-- Free variables

one : Held enc -> RegMap enc
one (InReg r) = singleton (slotOf r) r
one (OfStatic _) = empty

uses : All (HV enc) ctx -> Op ctx t -> RegMap enc
uses env (V x) = one (fetch x env)
uses _ _ = empty

usesAll : All (HV enc) ctx -> All (Op ctx) ts -> RegMap enc
usesAll env [] = empty
usesAll env (x :: xs) = mergeLeft (uses env x) (usesAll env xs)

usesList : All (HV enc) ctx -> List (Op ctx t) -> RegMap enc
usesList env = foldr (\x, m => mergeLeft (uses env x) m) empty

usesVect : All (HV enc) ctx -> Vect n (Op ctx t) -> RegMap enc
usesVect env = foldr (\x, m => mergeLeft (uses env x) m) empty

collect : All (HV enc) ctx -> {0 t : Ty enc} -> Op ctx t -> State (RegMap enc) (Op ctx t)
collect env x = do modify (mergeLeft (uses env x)); pure x

||| The registers of the environment an instruction reads.
instrUses : All (HV enc) ctx -> Instr d m (Var ctx) ts -> RegMap enc
instrUses env i = execState empty (traverseInstr (collect env) i)

------------------------------------------------------------------------------
-- The free variables of join blocks

||| A variable as its level: its position from the bottom of its context,
||| which does not change as the context grows.
Level : Type
Level = Nat

||| The level of a variable in a context of `depth` entries.
level : (depth : Nat) -> Var ctx t -> Level
level depth v = minus depth (S v.index)

opLevel : (depth : Nat) -> Op ctx t -> SortedSet Level
opLevel depth (V x) = singleton (level depth x)
opLevel _ _ = empty

opsLevels : (depth : Nat) -> All (Op ctx) ts -> SortedSet Level
opsLevels depth [] = empty
opsLevels depth (x :: xs) = union (opLevel depth x) (opsLevels depth xs)

listLevels : (depth : Nat) -> List (Op ctx t) -> SortedSet Level
listLevels depth = foldr (union . opLevel depth) empty

vectLevels : (depth : Nat) -> Vect n (Op ctx t) -> SortedSet Level
vectLevels depth = foldr (union . opLevel depth) empty

||| The levels an instruction reads.
instrLevels : (depth : Nat) -> Instr d m (Var ctx) ts -> SortedSet Level
instrLevels depth i = execState empty (traverseInstr (\x => do modify (union (opLevel depth x)); pure x) i)

||| The levels of a body's own first `n` binders, from `depth`, taken out of
||| what it reads: what is left, it reads from outside.
outside : (depth : Nat) -> (n : Nat) -> SortedSet Level -> SortedSet Level
outside depth Z s = s
outside depth (S n) s = outside (S depth) n (delete depth s)

||| What a join's block reads from outside: the depth of the join's context
||| and the levels below it, which the lowering of the join turns into the
||| registers of its environment.
JoinFrees : Type
JoinFrees = (Nat, SortedSet Level)

mutual
  ||| The levels a body reads of the variables bound outside it, directly or
  ||| through the blocks it jumps to (`lf` is what each label in scope reads);
  ||| and what each join's block reads, in the order the lowering meets the
  ||| joins: a join, then those in the code that reaches it, then those in
  ||| its block. Once for a whole body: computing a block's at its join read
  ||| the rest of the function again at every join, the square of its length.
  frees : Body d c m ls ctx -> (depth : Nat) -> All (\_ => SortedSet Level) ls ->
          (SortedSet Level, List JoinFrees -> List JoinFrees)
  frees (Bind {ts} i k) depth lf =
    let (fk, jk) = frees k (depth + length ts) lf
    in (union (instrLevels depth i) (outside depth (length ts) fk), jk)
  frees (Join ps b r) depth lf =
    let (fb, jb) = frees b (depth + length ps) (empty :: lf)
        block = outside depth (length ps) fb
        (fr, jr) = frees r depth (block :: lf)
    in (fr, \rest => (depth, block) :: jr (jb rest))
  frees (Jump l xs) depth lf = (union (fetch l lf) (opsLevels depth xs), id)
  frees (Branch _ x y a b) depth lf =
    let (fa, ja) = frees a depth lf
        (fb, jb) = frees b depth lf
    in (union (union (opLevel depth x) (opLevel depth y)) (union fa fb), ja . jb)
  frees (IfFixnums {n} vs y no) depth lf =
    let (fy, jy) = frees y (depth + S n) lf
        (fn, jn) = frees no depth lf
    in (union (vectLevels depth vs) (union (outside depth (S n) fy) fn), jy . jn)
  frees (ArithOv _ x y ok ovf) depth lf =
    let (fo, jo) = frees ok (S depth) lf
        (fv, jv) = frees ovf depth lf
    in (union (union (opLevel depth x) (opLevel depth y)) (union (outside depth 1 fo) fv), jo . jv)
  frees (TagOv x ok ovf) depth lf =
    let (fo, jo) = frees ok (S depth) lf
        (fv, jv) = frees ovf depth lf
    in (union (opLevel depth x) (union (outside depth 1 fo) fv), jo . jv)
  frees (Switch x _ bs dflt) depth lf =
    let (fc, jc) = freesCases bs depth lf
        (fd, jd) = frees dflt depth lf
    in (union (opLevel depth x) (union fc fd), jc . jd)
  frees (Call _ xs k) depth lf =
    let (fk, jk) = frees k (S depth) lf in (union (opsLevels depth xs) (outside depth 1 fk), jk)
  frees (TailCall _ xs) depth lf = (opsLevels depth xs, id)
  frees (Apply f x k) depth lf =
    let (fk, jk) = frees k (S depth) lf
    in (union (union (opLevel depth f) (opLevel depth x)) (outside depth 1 fk), jk)
  frees (TailApply f x) depth lf = (union (opLevel depth f) (opLevel depth x), id)
  frees (Return x) depth lf = (opLevel depth x, id)
  frees (Enter f xs) depth lf = (union (opLevel depth f) (listLevels depth xs), id)
  frees (Ret xs) depth lf = (opsLevels depth xs, id)
  frees (Crash _) depth lf = (empty, id)
  frees (Unsupported _) depth lf = (empty, id)

  freesCases : All (\_ => Body d c m ls ctx) ks -> (depth : Nat) -> All (\_ => SortedSet Level) ls ->
               (SortedSet Level, List JoinFrees -> List JoinFrees)
  freesCases [] depth lf = (empty, id)
  freesCases (b :: bs) depth lf =
    let (fb, jb) = frees b depth lf
        (fs, js) = freesCases bs depth lf
    in (union fb fs, jb . js)

------------------------------------------------------------------------------
-- The conversion's state

record St (enc : Enc) where
  constructor MkSt
  nextReg : Nat
  nextLabel : Nat
  ||| The blocks made so far, by label. Labels are taken in reading order.
  blocks : SortedMap BlockLabel (Block enc)
  ||| What the blocks of the joins still to be lowered read, in the order
  ||| the lowering meets them (`frees`).
  joins : List JoinFrees

M : Enc -> Type -> Type
M enc = State (St enc)

fresh : Ty enc -> M enc (R enc)
fresh t = do
  s <- get
  put ({ nextReg := S s.nextReg } s)
  pure (Slot s.nextReg t)

freshAll : (ts : List (Ty enc)) -> M enc (All (RV enc) ts)
freshAll [] = pure []
freshAll (t :: ts) = [| fresh t :: freshAll ts |]

freshLabel : M enc BlockLabel
freshLabel = do
  s <- get
  put ({ nextLabel := S s.nextLabel } s)
  pure s.nextLabel

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
      Just (InReg r) => insert (slotOf r) r m
      _ => m

||| A block's code: its instructions and its terminator.
Code : Enc -> Type
Code enc = (List (Instr enc), BlockTerminator enc)

addBlock : BlockLabel -> List (R enc) -> Code enc -> M enc ()
addBlock l ps (is, t) = modify { blocks $= insert l (MkBlock l ps is t) }

||| Code, with the registers of its environment it reads.
Lowered : Enc -> Type
Lowered enc = (RegMap enc, Code enc)

------------------------------------------------------------------------------
-- Operands

operand : All (HV enc) ctx -> Op ctx t -> Operand enc
operand env (V x) = case fetch x env of
  InReg r => R r
  OfStatic s => S s
operand env (W i) = Imm i
operand env (Fx i) = Imm i
operand env (Vx i) = Imm i
operand env Erased = Imm 0

operands : All (HV enc) ctx -> All (Op ctx) ts -> List (Operand enc)
operands env [] = []
operands env (x :: xs) = operand env x :: operands env xs

||| An operand in a register, with the instruction that materialises an
||| immediate.
asReg : All (HV enc) ctx -> Op ctx t -> M enc (List (Instr enc), R enc)
asReg env (V x) = case fetch x env of
  InReg r => pure ([], r)
  OfStatic s => do r <- fresh Val; pure ([LocatedIR.StaticAddr r s], r)
asReg env (W i) = do r <- fresh W64; pure ([Const r i], r)
asReg env (Fx {fx} i) = do r <- fresh Fix; pure ([Const r i], r)
asReg env (Vx {fx} i) = do r <- fresh Val; pure ([Const r i], r)
asReg env Erased = do r <- fresh Val; pure ([Const r 0], r)

||| An operand into a given register.
moveInto : All (HV enc) ctx -> R enc -> Op ctx t -> Instr enc
moveInto env d (V x) = case fetch x env of
  InReg r => Move d r
  OfStatic s => LocatedIR.StaticAddr d s
moveInto env d (W i) = Const d i
moveInto env d (Fx i) = Const d i
moveInto env d (Vx i) = Const d i
moveInto env d Erased = Const d 0

baseReg : All (HV enc) ctx -> Base (Var ctx) -> M enc (List (Instr enc), R enc)
baseReg env (AtWord x) = asReg env x
baseReg env (AtPtr x) = asReg env x

memRef : All (HV enc) ctx -> Mem (Var ctx) -> M enc (List (Instr enc), MemRef enc)
memRef env (MkMem b i o) = do
  (pb, rb) <- baseReg env b
  case i of
    Nothing => pure (pb, MkMemRef rb Nothing o)
    Just x => do (pi, ri) <- asReg env x; pure (pb ++ pi, MkMemRef rb (Just ri) o)

------------------------------------------------------------------------------
-- Instructions and bodies

parameters (d : Decls enc)
  nameOf : Var d.sigs s -> Name
  nameOf r = (entry d.sigs r).name

  collectsOf : Var d.sigs s -> Bool
  collectsOf r = case (entry d.sigs r).conv of
    InCPS => False
    InDirect _ col => col

  symOf : Var d.statics s -> Name
  symOf r = (entry d.statics r).sym

  ||| One register, through an instruction that reads it from an operand.
  unary : All (HV enc) ctx -> Op ctx t -> (R enc -> Instr enc) -> M enc (List (Instr enc))
  unary env x f = do (p, r) <- asReg env x; pure (p ++ [f r])

  binary : All (HV enc) ctx -> Op ctx t -> Op ctx u -> (R enc -> R enc -> Instr enc) ->
           M enc (List (Instr enc))
  binary env x y f = do (px, rx) <- asReg env x; (py, ry) <- asReg env y; pure (px ++ py ++ [f rx ry])

  intrinsic : All (HV enc) ctx -> IntrinsicName -> Maybe (R enc) -> List (Op ctx W64) -> M enc (List (Instr enc))
  intrinsic env n dst xs = pure [Intrinsic n dst (map (operand env) xs)]

  ||| The IR of an instruction binding the registers `ds`, given what is live
  ||| after it.
  instr : All (HV enc) ctx -> All (RV enc) ts -> (after : RegMap enc) -> Instr d m (Var ctx) ts ->
          M enc (List (Instr enc))
  instr env [r] _ (TermIR.FConst x) = pure [LocatedIR.FConst r x]
  instr env [r] _ (TermIR.CodeAddr f) = pure [LocatedIR.CodeAddr r (nameOf f)]
  -- not reached: `body` holds a static's address as itself, in no register
  instr env [r] _ (TermIR.StaticAddr s) = pure [LocatedIR.StaticAddr r (symOf s)]
  instr env [r] _ (TermIR.AreaAddr a) = pure [LocatedIR.AreaAddr r a]
  instr env [r] _ (TermIR.Arith o x y) = pure [LocatedIR.Arith o r (operand env x) (operand env y)]
  instr env [r] _ (TermIR.Unary o x) = unary env x (LocatedIR.Unary o r)
  instr env [r] _ (TermIR.Ext w s x) = unary env x (LocatedIR.Ext w s r)
  instr env [r] _ (TermIR.FArith o x y) = binary env x y (LocatedIR.FArith o r)
  instr env [r] _ (TermIR.FNeg x) = unary env x (LocatedIR.FNeg r)
  instr env [r] _ (TermIR.FCmp rel x y) = binary env x y (LocatedIR.FCmp rel r)
  instr env [r] _ (TermIR.Convert op x) = unary env x (LocatedIR.Convert op r)
  instr env [r] _ (TermIR.Cmp rel x y) = pure [LocatedIR.Cmp rel r (operand env x) (operand env y)]
  instr env [r] _ (TermIR.Load t mem) = do (p, m') <- memRef env mem; pure (p ++ [LocatedIR.Load t r m'])
  instr env [] _ (TermIR.Store t mem x) = do
    (p, m') <- memRef env mem
    (px, rx) <- asReg env x
    pure (p ++ px ++ [LocatedIR.Store t m' rx])
  instr env [r] _ (TermIR.LoadN w s mem) = do (p, m') <- memRef env mem; pure (p ++ [LocatedIR.LoadN w s r m'])
  instr env [] _ (TermIR.StoreN w mem x) = do
    (p, m') <- memRef env mem
    (px, rx) <- asReg env x
    pure (p ++ px ++ [LocatedIR.StoreN w m' rx])
  instr env [r] _ (TermIR.Tag {fx} x) = unary env x (LocatedIR.Tag r)
  instr env [r] _ (TermIR.Untag {fx} x) = unary env x (LocatedIR.Untag r)
  instr env [r] _ (TermIR.NarrowFix {fx} x) = unary env x (LocatedIR.Narrow Fix r)
  instr env [r] _ (TermIR.NarrowPtr k x) = unary env x (LocatedIR.Narrow (PtrTo k) r)
  instr env [r] _ (TermIR.WidenFix x) = unary env x (LocatedIR.Widen r)
  instr env [r] _ (TermIR.WidenPtr x) = unary env x (LocatedIR.Widen r)
  instr env [r] _ (TermIR.AddrToWord x) = unary env x (LocatedIR.AddrToWord r)
  instr env [r] _ (TermIR.WordToAddr k x) = unary env x (LocatedIR.WordToAddr k r)
  instr env [r] _ (TermIR.LoadHeader x) = unary env x (LocatedIR.LoadHeader r)
  instr env [r] _ (TermIR.LoadPart p x) = unary env x (LocatedIR.LoadPart p r)
  instr env [r] after (TermIR.AllocObj h fs) =
    -- the fields are written after the slow path's collection
    let live = values (mergeLeft after (usesAll env fs))
    in pure [LocatedIR.AllocObj r h (operands env fs) live]
  instr env [r] after (TermIR.AllocSized p n f) = do
    (pn, rn) <- asReg env n
    let fill = fillOf p f
        live = values (mergeLeft after (mergeLeft (one (InReg rn)) (maybe empty (fillUses p f) (Just ()))))
    pure (pn ++ [LocatedIR.AllocSized r p rn fill live])
    where
      fillOf : {0 kind : Kind} -> (q : HeaderPart kind) -> Fill (Var ctx) q -> Maybe (Operand enc)
      fillOf ArrayElems x = Just (operand env x)
      fillOf _ _ = Nothing
      fillUses : {0 kind : Kind} -> (q : HeaderPart kind) -> Fill (Var ctx) q -> () -> RegMap enc
      fillUses ArrayElems x _ = uses env x
      fillUses _ _ _ = empty
  instr env ds after (TermIR.DirectCall f xs) =
    pure [LocatedIR.DirectCall (nameOf f) (operands env xs) (regs ds) (collectsOf f) (values after)]
  instr env [r] _ TermIR.ReadHp = intrinsic env GetHp (Just r) []
  instr env [] _ (TermIR.WriteHp x) = intrinsic env SetHp Nothing [x]
  instr env [r] _ TermIR.ReadHpLim = intrinsic env GetHpLim (Just r) []
  instr env [] _ (TermIR.WriteHpLim x) = intrinsic env SetHpLim Nothing [x]
  instr env [r] _ TermIR.ReadK = pure [Intrinsic GetK (Just r) []]
  instr env [] _ (TermIR.WriteK x) = pure [Intrinsic SetK Nothing [operand env x]]
  instr env [r] _ TermIR.ReadStackPointer = intrinsic env GetStackPointer (Just r) []
  instr env [] _ (TermIR.WriteStackPointer x) = intrinsic env SetStackPointer Nothing [x]
  instr env [r] _ (TermIR.SystemCall n xs) = intrinsic env Syscall (Just r) (n :: toList xs)
  instr env [] _ (TermIR.Loc fc) = pure [LocatedIR.Loc fc]
  instr env [] _ (TermIR.Comment s) = pure [LocatedIR.Comment s]

  ||| A jump to a block: the arguments into its parameters. When an argument
  ||| reads one of those parameters, every argument goes into a fresh
  ||| register first, so that none is overwritten before it is read.
  jump : All (HV enc) ctx -> LabelInfo enc -> All (Op ctx) ps -> M enc (Code enc)
  jump env info xs =
    if any (\r => isJust (lookup (slotOf r) (usesAll env xs))) info.params
       then do
         (loads, temps) <- moves info.params xs
         pure (loads ++ zipWith Move info.params temps, LocatedIR.Jump info.label)
       else pure (direct info.params xs, LocatedIR.Jump info.label)
    where
      direct : List (R enc) -> All (Op ctx) qs -> List (Instr enc)
      direct (p :: ps) (x :: xs) = moveInto env p x :: direct ps xs
      direct _ _ = []

      moves : List (R enc) -> All (Op ctx) qs -> M enc (List (Instr enc), List (R enc))
      moves (p :: ps) (x :: xs) = do
        t <- fresh (regTy p)
        (is, ts) <- moves ps xs
        pure (moveInto env t x :: is, t :: ts)
      moves _ _ = pure ([], [])

  narrowAll : {auto 0 fx : HasFixnums enc.val} -> Vect n (R enc) ->
              M enc (List (Instr enc), All (RV enc) (replicate n (Fix {enc})))
  narrowAll [] = pure ([], [])
  narrowAll (r :: rs) = do
    f <- fresh Fix
    (is, fs) <- narrowAll rs
    pure (Narrow Fix f r :: is, f :: fs)

  mutual
    ||| Where a branch goes: a block of the body's own, or, when the body only
    ||| jumps to a block without parameters, that block.
    branchTo : Body d c m ls ctx -> All (HV enc) ctx -> All (LI enc) ls -> M enc (RegMap enc, BlockLabel)
    branchTo (Jump l []) env li = let info = fetch l li in pure (info.free, info.label)
    branchTo b env li = do
      lb <- freshLabel
      (fb, code) <- body b env li
      addBlock lb [] code
      pure (fb, lb)

    ||| The code of a body, and the registers of its environment it reads.
    ||| Labels are taken before the code under them is lowered, so that they
    ||| number the blocks in reading order.
    body : Body d c m ls ctx -> All (HV enc) ctx -> All (LI enc) ls -> M enc (Lowered enc)
    -- a static's address is held as itself, and so is the value it widens to
    body (Bind (TermIR.StaticAddr s) k) env li = body k (OfStatic (symOf s) :: env) li
    body (Bind (TermIR.WidenPtr (V x)) k) env li = case fetch x env of
      OfStatic s => body k (OfStatic s :: env) li
      InReg _ => bind [Val] (TermIR.WidenPtr (V x)) k env li
    body (Bind {ts} i k) env li = bind ts i k env li
    body (Join ps b r) env li = do
      l <- freshLabel
      params <- freshAll ps
      (depth, levels) <- popJoin
      let fb = registersAt env depth levels
          info = MkLabelInfo l (regs params) fb
      (fr, codeR) <- body r env (info :: li)
      (_, codeB) <- body b (append (held params) env) (info :: li)
      addBlock l [] codeB
      pure (fr, codeR)
    body (Jump l xs) env li = do
      let info = fetch l li
      code <- jump env info xs
      pure (mergeLeft info.free (usesAll env xs), code)
    body (Branch rel x y a b) env li = do
      (fa, la) <- branchTo a env li
      (fb, lb) <- branchTo b env li
      pure (mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft fa fb),
            ([], LocatedIR.Branch rel (operand env x) (operand env y) la lb))
    body (IfFixnums {fx} vs y no) env li = do
      ly <- freshLabel
      loaded <- traverse (asReg env) vs
      let rs = map snd loaded
      (narrows, fs) <- narrowAll rs
      (fy, (isY, tY)) <- body y (append (held fs) env) li
      addBlock ly [] (narrows ++ isY, tY)
      (fn, ln) <- branchTo no env li
      pure (mergeLeft (usesVect env vs) (mergeLeft (without (regs fs) fy) fn),
            (concatMap fst (toList loaded), IsFixnum (toList rs) ly ln))
    body (ArithOv {t} o x y ok ovf) env li = do
      f <- fresh t
      (fok, (isOk, tOk)) <- body ok (InReg f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft (without [f] fok) fov),
            (LocatedIR.ArithOv (ovArith o) f (operand env x) (operand env y) lo :: isOk, tOk))
    body (TagOv {fx} x ok ovf) env li = do
      (px, rx) <- asReg env x
      f <- fresh Fix
      (fok, (isOk, tOk)) <- body ok (InReg f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (uses env x) (mergeLeft (without [f] fok) fov),
            (px ++ LocatedIR.TagOv f rx lo :: isOk, tOk))
    body (Switch x keys bs dflt) env li = do
      (px, rx) <- asReg env x
      (fcs, labels) <- cases bs env li
      (fd, ld) <- branchTo dflt env li
      pure (mergeLeft (uses env x) (mergeLeft fcs fd), (px, LocatedIR.Switch rx (zip keys labels) ld))
    body (TermIR.Call f xs k) env li = do
      lr <- freshLabel
      r <- fresh Val
      (fk, codeK) <- body k (InReg r :: env) li
      let outer = without [r] fk
          live = values outer
      addBlock lr (live ++ [r]) codeK
      pure (mergeLeft (usesAll env xs) outer,
            ([], LocatedIR.Call (nameOf f) (operands env xs) (MkCont lr live)))
    body (TermIR.TailCall f xs) env li =
      pure (usesAll env xs, ([], LocatedIR.TailCall (nameOf f) (operands env xs)))
    body (TermIR.Apply f x k) env li = do
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      lr <- freshLabel
      r <- fresh Val
      (fk, codeK) <- body k (InReg r :: env) li
      let outer = without [r] fk
          live = values outer
      addBlock lr (live ++ [r]) codeK
      pure (mergeLeft (mergeLeft (uses env f) (uses env x)) outer,
            (pf ++ px, LocatedIR.Apply rf rx (MkCont lr live)))
    body (TermIR.TailApply f x) env li = do
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      pure (mergeLeft (uses env f) (uses env x), (pf ++ px, LocatedIR.TailApply rf rx))
    body (TermIR.Return x) env li = pure (uses env x, ([], LocatedIR.Return (operand env x)))
    body (TermIR.Enter f xs) env li = do
      (pf, rf) <- asReg env f
      pure (mergeLeft (uses env f) (usesList env xs), (pf, LocatedIR.Enter rf (map (operand env) xs)))
    body (TermIR.Ret xs) env li = pure (usesAll env xs, ([], LocatedIR.Ret (operands env xs)))
    body (TermIR.Crash s) env li = pure (empty, ([], LocatedIR.Crash s))
    body (TermIR.Unsupported s) env li = pure (empty, ([], LocatedIR.Unsupported s))

    ||| An instruction's registers, bound in the environment of the rest.
    bind : (ts : List (Ty enc)) -> Instr d m (Var ctx) ts -> Body d c m ls (ts ++ ctx) ->
           All (HV enc) ctx -> All (LI enc) ls -> M enc (Lowered enc)
    bind ts i k env li = do
      ds <- freshAll ts
      (after, (is, t)) <- body k (append (held ds) env) li
      let outer = without (regs ds) after
      pre <- instr env ds outer i
      pure (mergeLeft (instrUses env i) outer, (pre ++ is, t))

    ||| A switch's cases, each a block of its own, in order.
    cases : All (\_ => Body d c m ls ctx) ks -> All (HV enc) ctx -> All (LI enc) ls ->
            M enc (RegMap enc, List BlockLabel)
    cases [] env li = pure (empty, [])
    cases (b :: bs) env li = do
      (fb, l) <- branchTo b env li
      (fbs, ls) <- cases bs env li
      pure (mergeLeft fb fbs, l :: ls)

  function : (s : Sig enc) -> Body d s.conv s.converts [] s.params -> Function enc
  function s b =
    let run : M enc (List (R enc))
        run = do
          ps <- freshAll s.params
          modify { joins := snd (frees b (length s.params) []) [] }
          (_, code) <- body b (held ps) []
          addBlock 0 [] code
          pure (regs ps)
    in case runState (MkSt 0 1 empty []) run of
         (st, ps) => MkFunction s.name (conv s.conv) ps (results s.conv) 0 (values st.blocks) EmptyFC
    where
      conv : Conv enc -> CallingConvention
      conv InCPS = CPS
      conv (InDirect _ _) = Direct
      results : Conv enc -> List (Ty enc)
      results InCPS = []
      results (InDirect rs _) = rs

  functions : (ss : List (Sig enc)) -> All (Def d) ss -> List (Function enc)
  functions [] [] = []
  functions (s :: ss) (Defined b :: ds) = function s b :: functions ss ds
  functions (_ :: ss) (External :: ds) = functions ss ds

  field : SField d -> StaticField
  field (TermIR.SWord w) = LocatedIR.SWord w
  field (TermIR.SRef s) = LocatedIR.SRef (symOf s)
  field (TermIR.SCode f) = LocatedIR.SCode (nameOf f)

  statics : (ss : List StaticSig) -> All (StaticDef d) ss -> List (Static enc)
  statics [] [] = []
  statics (MkStaticSig sym k :: ss) (MkStaticDef h fs :: ds) = MkStatic sym k h (map field (toList fs)) :: statics ss ds

  entryName : Entry d -> Name
  entryName (MkEntry f) = nameOf f

||| The IR's programs, for producers that build terms and need not import
||| the IR, whose names the term's share.
public export
0 LocatedProgram : Enc -> Type
LocatedProgram enc = LocatedIR.Program enc

||| The program in the IR, for the target.
export
allocRegs : {d : Decls enc} -> Target -> TermIR.Program enc d -> LocatedIR.Program enc
allocRegs target (MkProgram fs ss e conIds) =
  LocatedIR.MkProgram target (functions d d.sigs fs) (statics d d.statics ss) (entryName d e) conIds
