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
||| join point's block is the exception: its jumps need its free registers
||| before it is lowered, so `free` computes them first, with a jump to the
||| block itself contributing nothing, the least fixed point.
module Compiler.Native.Allocate

import Compiler.Native.TermIR
import Compiler.Native.LocatedIR
import Compiler.Native.Target
import Control.Monad.State
import Data.SortedMap

%default total

------------------------------------------------------------------------------
-- Environments

R : Enc -> Type
R enc = Reg enc

RV : (enc : Enc) -> Ty enc -> Type
RV enc _ = R enc

MRV : (enc : Enc) -> Ty enc -> Type
MRV enc _ = Maybe (R enc)

||| Registers, by identity.
RegMap : Enc -> Type
RegMap enc = SortedMap Nat (R enc)

LV : (enc : Enc) -> List (Ty enc) -> Type
LV enc _ = RegMap enc

record LabelInfo (enc : Enc) where
  constructor MkLabelInfo
  label : BlockLabel
  params : List (R enc)
  ||| The registers the block reads from outside it, its parameters excluded.
  free : RegMap enc

LI : (enc : Enc) -> List (Ty enc) -> Type
LI enc _ = LabelInfo enc

justs : All (RV enc) ctx -> All (MRV enc) ctx
justs [] = []
justs (r :: rs) = Just r :: justs rs

nothings : (ts : List (Ty enc)) -> All (MRV enc) ts
nothings [] = []
nothings (_ :: ts) = Nothing :: nothings ts

append : All p xs -> All p ys -> All p (xs ++ ys)
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

frees : All (LI enc) ls -> All (LV enc) ls
frees [] = []
frees (i :: is) = i.free :: frees is

regs : All (RV enc) ts -> List (R enc)
regs [] = []
regs (r :: rs) = r :: regs rs

without : List (R enc) -> RegMap enc -> RegMap enc
without ds m = foldr (\d => delete (slotOf d)) m ds

------------------------------------------------------------------------------
-- Free variables

one : Maybe (R enc) -> RegMap enc
one (Just r) = singleton (slotOf r) r
one Nothing = empty

uses : All (MRV enc) ctx -> Op ctx t -> RegMap enc
uses env (V x) = one (fetch x env)
uses _ _ = empty

usesAll : All (MRV enc) ctx -> All (Op ctx) ts -> RegMap enc
usesAll env [] = empty
usesAll env (x :: xs) = mergeLeft (uses env x) (usesAll env xs)

usesList : All (MRV enc) ctx -> List (Op ctx t) -> RegMap enc
usesList env = foldr (\x, m => mergeLeft (uses env x) m) empty

usesVect : All (MRV enc) ctx -> Vect n (Op ctx t) -> RegMap enc
usesVect env = foldr (\x, m => mergeLeft (uses env x) m) empty

collect : All (MRV enc) ctx -> {0 t : Ty enc} -> Op ctx t -> State (RegMap enc) (Op ctx t)
collect env x = do modify (mergeLeft (uses env x)); pure x

||| The registers of the environment an instruction reads.
instrUses : All (MRV enc) ctx -> Instr d m (Var ctx) ts -> RegMap enc
instrUses env i = execState empty (traverseInstr (collect env) i)

mutual
  ||| The registers of the environment that the body reads, directly or
  ||| through the blocks it jumps to.
  free : Body d c m ls ctx -> All (MRV enc) ctx -> All (LV enc) ls -> RegMap enc
  free (Bind {ts} i k) env lf = mergeLeft (instrUses env i) (free k (append (nothings ts) env) lf)
  free (Join ps b r) env lf =
    let fb = free b (append (nothings ps) env) (empty :: lf)
    in free r env (fb :: lf)
  free (Jump l xs) env lf = mergeLeft (fetch l lf) (usesAll env xs)
  free (Branch _ x y a b) env lf =
    mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft (free a env lf) (free b env lf))
  free (IfFixnums {n} vs y no) env lf =
    mergeLeft (usesVect env vs) (mergeLeft (free y (append (nothings (replicate (S n) Fix)) env) lf) (free no env lf))
  free (ArithOv _ x y ok ovf) env lf =
    mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft (free ok (Nothing :: env) lf) (free ovf env lf))
  free (TagOv x ok ovf) env lf = mergeLeft (uses env x) (mergeLeft (free ok (Nothing :: env) lf) (free ovf env lf))
  free (Switch x _ bs dflt) env lf = mergeLeft (uses env x) (mergeLeft (freeCases bs env lf) (free dflt env lf))
  free (Call _ xs k) env lf = mergeLeft (usesAll env xs) (free k (Nothing :: env) lf)
  free (TailCall _ xs) env lf = usesAll env xs
  free (Apply f x k) env lf = mergeLeft (mergeLeft (uses env f) (uses env x)) (free k (Nothing :: env) lf)
  free (TailApply f x) env lf = mergeLeft (uses env f) (uses env x)
  free (Return x) env lf = uses env x
  free (Enter f xs) env lf = mergeLeft (uses env f) (usesList env xs)
  free (Ret xs) env lf = usesAll env xs
  free (Crash _) env lf = empty
  free (Unsupported _) env lf = empty

  freeCases : All (\_ => Body d c m ls ctx) ks -> All (MRV enc) ctx -> All (LV enc) ls -> RegMap enc
  freeCases [] env lf = empty
  freeCases (b :: bs) env lf = mergeLeft (free b env lf) (freeCases bs env lf)

------------------------------------------------------------------------------
-- The conversion's state

record St (enc : Enc) where
  constructor MkSt
  nextReg : Nat
  nextLabel : Nat
  ||| The blocks made so far, by label. Labels are taken in reading order.
  blocks : SortedMap BlockLabel (Block enc)

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

operand : All (RV enc) ctx -> Op ctx t -> Operand enc
operand env (V x) = R (fetch x env)
operand env (W i) = Imm i
operand env (Fx i) = Imm i
operand env (Vx i) = Imm i
operand env Erased = Imm 0

operands : All (RV enc) ctx -> All (Op ctx) ts -> List (Operand enc)
operands env [] = []
operands env (x :: xs) = operand env x :: operands env xs

||| An operand in a register, with the instruction that materialises an
||| immediate.
asReg : All (RV enc) ctx -> Op ctx t -> M enc (List (Instr enc), R enc)
asReg env (V x) = pure ([], fetch x env)
asReg env (W i) = do r <- fresh W64; pure ([Const r i], r)
asReg env (Fx {fx} i) = do r <- fresh Fix; pure ([Const r i], r)
asReg env (Vx {fx} i) = do r <- fresh Val; pure ([Const r i], r)
asReg env Erased = do r <- fresh Val; pure ([Const r 0], r)

||| An operand into a given register.
moveInto : All (RV enc) ctx -> R enc -> Op ctx t -> Instr enc
moveInto env d (V x) = Move d (fetch x env)
moveInto env d (W i) = Const d i
moveInto env d (Fx i) = Const d i
moveInto env d (Vx i) = Const d i
moveInto env d Erased = Const d 0

baseReg : All (RV enc) ctx -> Base (Var ctx) -> M enc (List (Instr enc), R enc)
baseReg env (AtWord x) = asReg env x
baseReg env (AtPtr x) = asReg env x

memRef : All (RV enc) ctx -> Mem (Var ctx) -> M enc (List (Instr enc), MemRef enc)
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
  unary : All (RV enc) ctx -> Op ctx t -> (R enc -> Instr enc) -> M enc (List (Instr enc))
  unary env x f = do (p, r) <- asReg env x; pure (p ++ [f r])

  binary : All (RV enc) ctx -> Op ctx t -> Op ctx u -> (R enc -> R enc -> Instr enc) ->
           M enc (List (Instr enc))
  binary env x y f = do (px, rx) <- asReg env x; (py, ry) <- asReg env y; pure (px ++ py ++ [f rx ry])

  intrinsic : All (RV enc) ctx -> IntrinsicName -> Maybe (R enc) -> List (Op ctx W64) -> M enc (List (Instr enc))
  intrinsic env n dst xs = pure [Intrinsic n dst (map (operand env) xs)]

  ||| The IR of an instruction binding the registers `ds`, given what is live
  ||| after it.
  instr : All (RV enc) ctx -> All (RV enc) ts -> (after : RegMap enc) -> Instr d m (Var ctx) ts ->
          M enc (List (Instr enc))
  instr env [r] _ (TermIR.FConst x) = pure [LocatedIR.FConst r x]
  instr env [r] _ (TermIR.CodeAddr f) = pure [LocatedIR.CodeAddr r (nameOf f)]
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
    let live = values (mergeLeft after (usesAll (justs env) fs))
    in pure [LocatedIR.AllocObj r h (operands env fs) live]
  instr env [r] after (TermIR.AllocSized p n f) = do
    (pn, rn) <- asReg env n
    let fill = fillOf p f
        live = values (mergeLeft after (mergeLeft (one (Just rn)) (maybe empty (fillUses p f) (Just ()))))
    pure (pn ++ [LocatedIR.AllocSized r p rn fill live])
    where
      fillOf : {0 kind : Kind} -> (q : HeaderPart kind) -> Fill (Var ctx) q -> Maybe (Operand enc)
      fillOf ArrayElems x = Just (operand env x)
      fillOf _ _ = Nothing
      fillUses : {0 kind : Kind} -> (q : HeaderPart kind) -> Fill (Var ctx) q -> () -> RegMap enc
      fillUses ArrayElems x _ = uses (justs env) x
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
  jump : All (RV enc) ctx -> LabelInfo enc -> All (Op ctx) ps -> M enc (Code enc)
  jump env info xs =
    if any (\r => isJust (lookup (slotOf r) (usesAll (justs env) xs))) info.params
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
    branchTo : Body d c m ls ctx -> All (RV enc) ctx -> All (LI enc) ls -> M enc (RegMap enc, BlockLabel)
    branchTo (Jump l []) env li = let info = fetch l li in pure (info.free, info.label)
    branchTo b env li = do
      lb <- freshLabel
      (fb, code) <- body b env li
      addBlock lb [] code
      pure (fb, lb)

    ||| The code of a body, and the registers of its environment it reads.
    ||| Labels are taken before the code under them is lowered, so that they
    ||| number the blocks in reading order.
    body : Body d c m ls ctx -> All (RV enc) ctx -> All (LI enc) ls -> M enc (Lowered enc)
    body (Bind {ts} i k) env li = do
      ds <- freshAll ts
      (after, (is, t)) <- body k (append ds env) li
      let outer = without (regs ds) after
      pre <- instr env ds outer i
      pure (mergeLeft (instrUses (justs env) i) outer, (pre ++ is, t))
    body (Join ps b r) env li = do
      l <- freshLabel
      params <- freshAll ps
      let fb = free b (append (nothings ps) (justs env)) (empty :: frees li)
          info = MkLabelInfo l (regs params) fb
      (fr, codeR) <- body r env (info :: li)
      (_, codeB) <- body b (append params env) (info :: li)
      addBlock l [] codeB
      pure (fr, codeR)
    body (Jump l xs) env li = do
      let info = fetch l li
      code <- jump env info xs
      pure (mergeLeft info.free (usesAll (justs env) xs), code)
    body (Branch rel x y a b) env li = do
      (fa, la) <- branchTo a env li
      (fb, lb) <- branchTo b env li
      pure (mergeLeft (mergeLeft (uses (justs env) x) (uses (justs env) y)) (mergeLeft fa fb),
            ([], LocatedIR.Branch rel (operand env x) (operand env y) la lb))
    body (IfFixnums {fx} vs y no) env li = do
      ly <- freshLabel
      loaded <- traverse (asReg env) vs
      let rs = map snd loaded
      (narrows, fs) <- narrowAll rs
      (fy, (isY, tY)) <- body y (append fs env) li
      addBlock ly [] (narrows ++ isY, tY)
      (fn, ln) <- branchTo no env li
      pure (mergeLeft (usesVect (justs env) vs) (mergeLeft (without (regs fs) fy) fn),
            (concatMap fst (toList loaded), IsFixnum (toList rs) ly ln))
    body (ArithOv {t} o x y ok ovf) env li = do
      f <- fresh t
      (fok, (isOk, tOk)) <- body ok (f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (mergeLeft (uses (justs env) x) (uses (justs env) y)) (mergeLeft (without [f] fok) fov),
            (LocatedIR.ArithOv (ovArith o) f (operand env x) (operand env y) lo :: isOk, tOk))
    body (TagOv {fx} x ok ovf) env li = do
      (px, rx) <- asReg env x
      f <- fresh Fix
      (fok, (isOk, tOk)) <- body ok (f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (uses (justs env) x) (mergeLeft (without [f] fok) fov),
            (px ++ LocatedIR.TagOv f rx lo :: isOk, tOk))
    body (Switch x keys bs dflt) env li = do
      (px, rx) <- asReg env x
      (fcs, labels) <- cases bs env li
      (fd, ld) <- branchTo dflt env li
      pure (mergeLeft (uses (justs env) x) (mergeLeft fcs fd), (px, LocatedIR.Switch rx (zip keys labels) ld))
    body (TermIR.Call f xs k) env li = do
      lr <- freshLabel
      r <- fresh Val
      (fk, codeK) <- body k (r :: env) li
      let outer = without [r] fk
          live = values outer
      addBlock lr (live ++ [r]) codeK
      pure (mergeLeft (usesAll (justs env) xs) outer,
            ([], LocatedIR.Call (nameOf f) (operands env xs) (MkCont lr live)))
    body (TermIR.TailCall f xs) env li =
      pure (usesAll (justs env) xs, ([], LocatedIR.TailCall (nameOf f) (operands env xs)))
    body (TermIR.Apply f x k) env li = do
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      lr <- freshLabel
      r <- fresh Val
      (fk, codeK) <- body k (r :: env) li
      let outer = without [r] fk
          live = values outer
      addBlock lr (live ++ [r]) codeK
      pure (mergeLeft (mergeLeft (uses (justs env) f) (uses (justs env) x)) outer,
            (pf ++ px, LocatedIR.Apply rf rx (MkCont lr live)))
    body (TermIR.TailApply f x) env li = do
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      pure (mergeLeft (uses (justs env) f) (uses (justs env) x), (pf ++ px, LocatedIR.TailApply rf rx))
    body (TermIR.Return x) env li = pure (uses (justs env) x, ([], LocatedIR.Return (operand env x)))
    body (TermIR.Enter f xs) env li = do
      (pf, rf) <- asReg env f
      pure (mergeLeft (uses (justs env) f) (usesList (justs env) xs), (pf, LocatedIR.Enter rf (map (operand env) xs)))
    body (TermIR.Ret xs) env li = pure (usesAll (justs env) xs, ([], LocatedIR.Ret (operands env xs)))
    body (TermIR.Crash s) env li = pure (empty, ([], LocatedIR.Crash s))
    body (TermIR.Unsupported s) env li = pure (empty, ([], LocatedIR.Unsupported s))

    ||| A switch's cases, each a block of its own, in order.
    cases : All (\_ => Body d c m ls ctx) ks -> All (RV enc) ctx -> All (LI enc) ls ->
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
          (_, code) <- body b ps []
          addBlock 0 [] code
          pure (regs ps)
    in case runState (MkSt 0 1 empty) run of
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
allocate : {d : Decls enc} -> Target -> TermIR.Program enc d -> LocatedIR.Program enc
allocate target (MkProgram fs ss e conIds) =
  LocatedIR.MkProgram target (functions d d.sigs fs) (statics d d.statics ss) (entryName d e) conIds
