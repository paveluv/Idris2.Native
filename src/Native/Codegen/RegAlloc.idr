||| Register allocation: the term IR (`Native.Codegen.TermIR.Program`) into the
||| located IR (`Native.Codegen.LocatedIR.Program`), spill-everything for now.
|||
||| Every binding gets a `SCRATCH` slot of its own, but a retyping's: a byte
||| address and its word are one register, so the retyping between them
||| binds its operand's slot under the other type, and has no code. A value
||| is never redefined, so a variable is the same slot wherever it is in
||| scope, and a slot holds values of one type, or the two raw types a
||| retyping joins, neither of which the collector sees. No value is in a
||| register. A join point becomes a block, and its parameters
||| locations that each jump assigns at once, by a parallel move
||| (`LocatedIR.Instr.Par`), which reads every argument before it writes a
||| parameter. A call's continuation becomes a resume block. An
||| immediate where the IR wants a register is materialised just before its
||| use.
|||
||| An environment, how each variable of a body's context is held, and the
||| blocks' labels in scope are random-access lists (`Native.Data.RAList`):
||| a variable is read in steps of the order of the logarithm of its
||| context's length, however far below the top it was bound.
|||
||| What is live is computed, not stored. Lowering a body returns, with its
||| code, the registers of its environment it reads, directly or through
||| the blocks it jumps to; so live across an instruction, an allocation or
||| a call is what lowering the code after it returned, in the same pass. A
||| join point's block is the exception: its jumps need its free variables
||| before it is lowered, so `frees` computes them first, once for the whole
||| body, as levels. A jump to the block itself contributes nothing to the
||| block's own set, the least fixed point, but a join inside a loop's block
||| that jumps back to the loop reads the loop's set, so its set is
||| completed with it once that is known.
module Native.Codegen.RegAlloc

import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Cont as LocatedIR
import Native.Codegen.LocatedIR.Content as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Label as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Mem as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Static as LocatedIR
import Native.Codegen.LocatedIR.Step as LocatedIR
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

import Core.FC
import Core.Name
import Data.Fin
import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.Singleton
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Data.Zippable
import Native.Data.Builder as Data
import Native.Data.Distinct
import Native.Data.Level
import Native.Data.RAList as Data
import Native.Data.Stateful as Data
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

------------------------------------------------------------------------------
-- Environments

RV : (enc : Types.Enc) -> IRCommon.Ty enc -> Type
RV enc t = LocatedIR.Location enc t

||| How a variable of the environment is held: in a register, or as the
||| address of a static object, which needs none. A static never moves, so
||| its address is an operand where it is used (`S`), never live across an
||| allocation and never in a slot. The term binds one by `StaticAddr` and
||| widens it to a value by `WidenPtr`; the environment holds both as the
||| static.
data Held : (enc : Types.Enc) -> IRCommon.Ty enc -> Type where
  InReg : (def : Nat) -> LocatedIR.Location enc t -> Held enc t
  OfStatic : Name -> (t : IRCommon.Ty enc) -> Held enc t

HV : (enc : Types.Enc) -> IRCommon.Ty enc -> Type
HV enc t = Held enc t

||| Registers, by identity, with what each holds.
RegMap : Types.Enc -> Type
RegMap enc = SortedMap Nat (LocatedIR.Content, LocatedIR.Location.Place enc)

||| The registers of the map.
places : RegMap enc -> List (LocatedIR.Location.Place enc)
places m = map snd (values m)

record LabelInfo (enc : Types.Enc) (ps : List (IRCommon.Ty enc)) where
  constructor MkLabelInfo
  label : LocatedIR.Label
  params : All (RV enc) ps
  ||| The registers the block reads from outside it, its parameters excluded.
  free : RegMap enc

LI : (enc : Types.Enc) -> List (IRCommon.Ty enc) -> Type
LI enc ps = LabelInfo enc ps

regs : All (RV enc) ts -> List (LocatedIR.Location.Place enc)
regs [] = []
regs (r :: rs) = LocatedIR.Location.At r :: regs rs

||| Registers, as the environment holds them.
held : (first : Nat) -> All (RV enc) ts -> All (HV enc) ts
held _ [] = []
held n (r :: rs) = InReg n r :: held (S n) rs

||| Registers holding the values of the definitions numbered from `first`,
||| as a certificate states them.
entries : (first : Nat) -> All (RV enc) ts -> List (LocatedIR.Content, LocatedIR.Location.Place enc)
entries _ [] = []
entries n (r :: rs) = (LocatedIR.Content.Value n, LocatedIR.Location.At r) :: entries (S n) rs

||| The number the allocator knows a location by, a slot's: it keeps every
||| value in a slot of its own, so the locations it holds are slots.
number : LocatedIR.Location.Place enc -> Nat
number (LocatedIR.Location.At (LocatedIR.Location.Slot n _)) = n
number (LocatedIR.Location.At (LocatedIR.Location.Register _ _)) = 0

without : List (LocatedIR.Location.Place enc) -> RegMap enc -> RegMap enc
without ds m = foldr (\d => delete (number d)) m ds

------------------------------------------------------------------------------
-- Free variables

one : Held enc t -> RegMap enc
one (InReg v r) =
  singleton (number (LocatedIR.Location.At r)) (LocatedIR.Content.Value v, LocatedIR.Location.At r)
one (OfStatic _ _) = empty

uses : Data.RAList (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t -> RegMap enc
uses env (TermIR.Opnd.V x) = one (TermIR.Var.fetch x env)
uses _ _ = empty

usesAll : Data.RAList (HV enc) ctx -> All (TermIR.Opnd (TermIR.Var ctx)) ts -> RegMap enc
usesAll env [] = empty
usesAll env (x :: xs) = mergeLeft (uses env x) (usesAll env xs)

------------------------------------------------------------------------------
-- The free variables of join blocks

||| A variable as its level: its position from the bottom of its context,
||| which does not change as the context grows.
Level : Type
Level = Nat

||| What code reads from outside it, as `frees` computes it: `Left` a
||| variable, by its level; `Right`, through a jump to a join whose block is
||| still being computed (a loop's, from the loop's block or a join's inside
||| it), whatever that block reads, by the level of the join's label among
||| the labels in scope.
Read : Type
Read = Either Level Nat

||| What a join's block reads from outside: the depth of the join's context
||| and the levels below it, which the lowering of the join turns into the
||| registers of its environment.
JoinFrees : Type
JoinFrees = (Nat, SortedSet Read)

------------------------------------------------------------------------------
-- The conversion's state

record St (enc : Types.Enc) where
  constructor MkSt
  nextReg : Nat
  ||| The number of the term's next definition (`freshDefs`).
  nextDef : Nat
  nextLabel : Nat
  ||| The blocks made so far, by label. Labels are taken in reading order.
  blocks : SortedMap LocatedIR.Label (LocatedIR.Block enc)
  ||| What the blocks of the joins still to be lowered read, in the order
  ||| the lowering meets them (`frees`).
  joins : List JoinFrees

M : Types.Enc -> Type -> Type
M enc = Data.Stateful (St enc) Void

fresh : (t : IRCommon.Ty enc) -> M enc (LocatedIR.Location enc t)
fresh t =
  Data.Stateful.state (\s => ({ nextReg := S s.nextReg } s, LocatedIR.Location.Slot s.nextReg t))

freshAll : (ts : List (IRCommon.Ty enc)) -> M enc (All (RV enc) ts)
freshAll [] = pure []
freshAll (t :: ts) = [| fresh t :: freshAll ts |]

||| The numbers of the term's next `n` definitions, the first of them: the
||| lowering numbers every definition as it meets it, each node's when its
||| lowering begins, before anything under it, so that the allocation
||| check, which numbers the term in the same order, knows which
||| definition each operation realises. A node that binds values numbers
||| them, one each (an instruction's results, a join's parameters, a
||| call's result, an overflow's, a fixnum test's narrowings), and one
||| that binds none takes one number (a terminator, a store), the numbers
||| of a node's values its own.
freshDefs : Nat -> M enc Nat
freshDefs n = Data.Stateful.state (\s => ({ nextDef := s.nextDef + n } s, s.nextDef))

freshLabel : M enc LocatedIR.Label
freshLabel = Data.Stateful.state (\s => ({ nextLabel := S s.nextLabel } s, s.nextLabel))

||| A block's code: its instructions, as the lowering produces them, and
||| its terminator.
Code : Types.Enc -> Type
Code enc = (Data.Builder (LocatedIR.Step enc), (Nat, LocatedIR.Terminator enc))

||| A block, of its parameters, its certificate (`Block.cert`) and its code.
addBlock : LocatedIR.Label -> List (LocatedIR.Location.Place enc) ->
           List (LocatedIR.Content, LocatedIR.Location.Place enc) -> Code enc -> M enc ()
addBlock l ps cert (is, (n, t)) =
  Data.Stateful.modify { blocks $= insert l (LocatedIR.MkBlock l ps cert (toList is) t n) }

||| Code, with the registers of its environment it reads.
Lowered : Types.Enc -> Type
Lowered enc = (RegMap enc, Code enc)

------------------------------------------------------------------------------
-- Operands

operand : Data.RAList (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t -> LocatedIR.Opnd enc t
operand env (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
  InReg _ r => LocatedIR.Opnd.R r
  OfStatic s _ => LocatedIR.Opnd.StaticRef s
operand env (TermIR.Opnd.W i) = LocatedIR.Opnd.Imm i
operand env (TermIR.Opnd.Fx i) = LocatedIR.Opnd.Imm i
operand env (TermIR.Opnd.Vx i) = LocatedIR.Opnd.Imm i
operand env TermIR.Opnd.Erased = LocatedIR.Opnd.Imm 0

operands : Data.RAList (HV enc) ctx -> All (TermIR.Opnd (TermIR.Var ctx)) ts ->
           List (LocatedIR.Opnd.Arg enc)
operands env [] = []
operands env (x :: xs) = LocatedIR.Opnd.MkArg (operand env x) :: operands env xs

||| Operands that are all words, as the located IR's list of them.
wordOperands : Data.RAList (HV enc) ctx -> {k : Nat} ->
               All (TermIR.Opnd (TermIR.Var ctx)) (replicate k IRCommon.Ty.W64) ->
               List (LocatedIR.Opnd enc IRCommon.Ty.W64)
wordOperands env {k = Z} [] = []
wordOperands env {k = S k'} (x :: xs) = operand env x :: wordOperands env xs

||| What an operand is: a definition's value, or one register allocation
||| puts into a register for it.
content : Data.RAList (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t -> LocatedIR.Content
content env (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
  InReg v _ => LocatedIR.Content.Value v
  OfStatic s _ => LocatedIR.Content.Put (LocatedIR.Step.StaticAddress s)
content env (TermIR.Opnd.W i) = LocatedIR.Content.Put (LocatedIR.Step.Immediate i)
content env (TermIR.Opnd.Fx i) = LocatedIR.Content.Put (LocatedIR.Step.Immediate i)
content env (TermIR.Opnd.Vx i) = LocatedIR.Content.Put (LocatedIR.Step.Immediate i)
content env TermIR.Opnd.Erased = LocatedIR.Content.Put (LocatedIR.Step.Immediate 0)

||| A value put into a location, and an immediate.
remat : LocatedIR.Location enc t -> LocatedIR.Step.Materialised -> LocatedIR.Step enc
remat = LocatedIR.Step.Remat

immediate : LocatedIR.Location enc t -> Int64 -> LocatedIR.Step enc
immediate r i = LocatedIR.Step.Remat r (LocatedIR.Step.Immediate i)

||| An operand in a register, with the shuffle that puts an immediate or a
||| static's address into one.
asReg : Data.RAList (HV enc) ctx -> TermIR.Opnd (TermIR.Var ctx) t ->
        M enc (List (LocatedIR.Step enc), LocatedIR.Location enc t)
asReg env (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
  InReg _ r => pure ([], r)
  OfStatic s t' => do r <- fresh t'; pure ([remat r (LocatedIR.Step.StaticAddress s)], r)
asReg env (TermIR.Opnd.W i) = do r <- fresh IRCommon.Ty.W64; pure ([immediate r i], r)
asReg env (TermIR.Opnd.Fx {fx} i) = do r <- fresh IRCommon.Ty.Fix; pure ([immediate r i], r)
asReg env (TermIR.Opnd.Vx {fx} i) = do r <- fresh IRCommon.Ty.Val; pure ([immediate r i], r)
asReg env TermIR.Opnd.Erased = do r <- fresh IRCommon.Ty.Val; pure ([immediate r 0], r)

------------------------------------------------------------------------------
-- Instructions and bodies

||| The program's declarations, each list as a random-access list of its
||| own entries (`RAList.fromList`), made once for the program: a variable
||| that names a callee or a static is resolved in steps of the order of
||| the logarithm of their number, where a walk of the list takes as many
||| as the variable's position.
record Declared (d : TermIR.Decls enc) where
  constructor MkDeclared
  sigs : Data.RAList Singleton d.sigs
  statics : Data.RAList Singleton d.statics

parameters {enc : Types.Enc} {0 d : TermIR.Decls enc} (declared : Declared d)
  varName : TermIR.Var d.sigs s -> Name
  varName r = (TermIR.Var.entry declared.sigs r).name

  varSym : TermIR.Var d.statics s -> Name
  varSym r = (TermIR.Var.entry declared.statics r).sym

  mutual
    ||| Where a branch goes: a block of the body's own, or, when the body only
    ||| jumps to a block without parameters, that block.
    branchTo : TermIR.Body d c m ls ctx -> Data.RAList (HV enc) ctx -> Data.RAList (LI enc) ls ->
               M enc (RegMap enc, LocatedIR.Label)
    -- the jump's number taken though it is no block's
    branchTo (TermIR.Body.Jump l []) env li = do
      _ <- freshDefs 1
      let info = TermIR.Var.fetch l li
      pure (info.free, info.label)
    branchTo b env li = do
      lb <- freshLabel
      (fb, code) <- body b env li
      addBlock lb [] (values fb) code
      pure (fb, lb)

    ||| The code of a body, and the registers of its environment it reads.
    ||| Labels are taken before the code under them is lowered, so that they
    ||| number the blocks in reading order.
    body : TermIR.Body d c m ls ctx -> Data.RAList (HV enc) ctx -> Data.RAList (LI enc) ls ->
           M enc (Lowered enc)
    -- a static's address is held as itself, and so is the value it widens to
    body (TermIR.Body.Bind {ts = [IRCommon.Ty.PtrTo kd]} (TermIR.Instr.StaticAddr s) k) env li = do
      _ <- freshDefs 1
      body k (OfStatic (varSym s) (IRCommon.Ty.PtrTo kd) :: env) li
    body (TermIR.Body.Bind (TermIR.Instr.WidenPtr (TermIR.Opnd.V x)) k) env li =
      case TermIR.Var.fetch x env of
      OfStatic s _ => do _ <- freshDefs 1; body k (OfStatic s IRCommon.Ty.Val :: env) li
      InReg _ _ => bind [IRCommon.Ty.Val] (TermIR.Instr.WidenPtr (TermIR.Opnd.V x)) k env li
    body (TermIR.Body.Bind {ts} i k) env li = bind ts i k env li
    body (TermIR.Body.Join ps b r) env li = do
      l <- freshLabel
      params <- freshAll ps
      first <- freshDefs (length ps)
      (depth, levels) <- popJoin
      let fb = registersAt env depth levels
          li' = MkLabelInfo l params fb :: li
      (fr, codeR) <- body r env li'
      (_, codeB) <- body b (Data.RAList.prepend (held first params) env) li'
      addBlock l [] (entries first params ++ values fb) codeB
      pure (fr, codeR)
      where
        ||| What the next join's block reads.
        popJoin : M enc JoinFrees
        popJoin = do
          s <- Data.Stateful.get
          case s.joins of
            j :: js => do Data.Stateful.put ({ joins := js } s); pure j
            [] => pure (0, empty)

        ||| The registers of the environment, `depth` deep, at the levels.
        registersAt : Data.RAList (HV enc) ctx -> (depth : Nat) -> SortedSet Read -> RegMap enc
        registersAt env depth lvs = foldl add empty (Prelude.toList lvs)
          where
            add : RegMap enc -> Read -> RegMap enc
            add m (Left l) = case Data.RAList.lookup (Data.Level.position depth l) env of
              Just (Data.RAList.MkFound (InReg v r) _) =>
                insert (number (LocatedIR.Location.At r))
                  (LocatedIR.Content.Value v, LocatedIR.Location.At r) m
              _ => m
            add m (Right _) = m
    body (TermIR.Body.Jump l xs) env li = do
      n <- freshDefs 1
      let info = TermIR.Var.fetch l li
      code <- jump n env info xs
      pure (mergeLeft info.free (usesAll env xs), code)
      where
        ||| A jump to a block: the arguments into its parameters, at once. Those
        ||| in locations by one parallel move, which reads every argument
        ||| before it writes a parameter, an argument that is a parameter
        ||| included; then the constants and statics, which read nothing.
        jump : Nat -> Data.RAList (HV enc) ctx -> LabelInfo enc ps ->
               All (TermIR.Opnd (TermIR.Var ctx)) ps -> M enc (Code enc)
        jump n env info xs =
          let (ms, rest) = args info.params xs
          in pure (Data.Builder.piece ((if null ms then [] else [LocatedIR.Step.Par ms]) ++ rest),
                   (n, LocatedIR.Terminator.Jump info.label))
          where
            ||| The arguments in locations, each a copy into its parameter; and
            ||| the others into their parameters.
            args : All (RV enc) qs -> All (TermIR.Opnd (TermIR.Var ctx)) qs ->
                   (List (LocatedIR.Step.Copy enc), List (LocatedIR.Step enc))
            args (p :: ps) (x :: xs') =
              let (ms, is) = args ps xs' in
              case x of
                TermIR.Opnd.V v => case TermIR.Var.fetch v env of
                  InReg _ r => (LocatedIR.Step.MkCopy p r :: ms, is)
                  OfStatic s _ => (ms, remat p (LocatedIR.Step.StaticAddress s) :: is)
                TermIR.Opnd.W i => (ms, immediate p i :: is)
                TermIR.Opnd.Fx i => (ms, immediate p i :: is)
                TermIR.Opnd.Vx i => (ms, immediate p i :: is)
                TermIR.Opnd.Erased => (ms, immediate p 0 :: is)
            args [] [] = ([], [])
    body (TermIR.Body.Branch rel x y a b) env li = do
      n <- freshDefs 1
      (fa, la) <- branchTo a env li
      (fb, lb) <- branchTo b env li
      pure (mergeLeft (mergeLeft (uses env x) (uses env y)) (mergeLeft fa fb),
            (neutral, (n, LocatedIR.Terminator.Branch rel (operand env x) (operand env y) la lb)))
    body (TermIR.Body.IfFixnums {fx} vs y no) env li = do
      n <- freshDefs 1
      ly <- freshLabel
      loaded <- traverse (asReg env) vs
      let rs = map snd loaded
      first <- freshDefs (length vs)
      (narrows, fs) <- narrowAll first rs
      (fy, (isY, tY)) <- body y (Data.RAList.prepend (held first fs) env) li
      -- the values tested, read by their narrowings in the yes block, and
      -- what the rest of it reads
      let tested = fromList (toList (zipWith (\v, r => (number (LocatedIR.Location.At r),
                                                          (content env v, LocatedIR.Location.At r)))
                                              vs rs))
      addBlock ly [] (values (mergeLeft tested (without (regs fs) fy)))
        (Data.Builder.piece narrows <+> isY, tY)
      (fn, ln) <- branchTo no env li
      pure (mergeLeft (usesVect env vs) (mergeLeft (without (regs fs) fy) fn),
            (concatMap (Data.Builder.piece . fst) (toList loaded),
              (n, LocatedIR.Terminator.IfFixnums (toList rs) ly ln)))
      where
        usesVect : Data.RAList (HV enc) ctx -> Vect n (TermIR.Opnd (TermIR.Var ctx) t) -> RegMap enc
        usesVect env = foldr (\x, m => mergeLeft (uses env x) m) empty

        -- each narrowing a definition of its own, numbered from `k`
        narrowAll : (k : Nat) -> Vect n' (LocatedIR.Location enc IRCommon.Ty.Val) ->
                    M enc (List (LocatedIR.Step enc),
                           All (RV enc) (replicate n' (IRCommon.Ty.Fix {enc})))
        narrowAll _ [] = pure ([], [])
        narrowAll k (r :: rs) = do
          f <- fresh IRCommon.Ty.Fix
          (is, fs) <- narrowAll (S k) rs
          pure (LocatedIR.Step.Op k (LocatedIR.Instr.Narrow IRCommon.Ty.Fix f r) :: is, f :: fs)
    body (TermIR.Body.ArithOv {t} o x y ok ovf) env li = do
      n <- freshDefs 1
      f <- fresh t
      (fok, (isOk, tOk)) <- body ok (InReg n f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure
        (mergeLeft (mergeLeft (uses env x) (uses env y))
         (mergeLeft (without [LocatedIR.Location.At f] fok) fov),
            (Data.Builder.single
              (LocatedIR.Step.Op n
                (LocatedIR.Instr.ArithOv (TermIR.OvOp.ovArith o) f (operand env x) (operand env y)
                  lo))
              <+> isOk, tOk))
    body (TermIR.Body.TagOv {fx} x ok ovf) env li = do
      n <- freshDefs 1
      (px, rx) <- asReg env x
      f <- fresh IRCommon.Ty.Fix
      (fok, (isOk, tOk)) <- body ok (InReg n f :: env) li
      (fov, lo) <- branchTo ovf env li
      pure (mergeLeft (uses env x) (mergeLeft (without [LocatedIR.Location.At f] fok) fov),
            (Data.Builder.piece (px ++ [LocatedIR.Step.Op n (LocatedIR.Instr.TagOv f rx lo)])
             <+> isOk, tOk))
    body (TermIR.Body.Switch x keys bs dflt) env li = do
      n <- freshDefs 1
      (px, rx) <- asReg env x
      (fcs, labels) <- cases bs env li
      (fd, ld) <- branchTo dflt env li
      pure (mergeLeft (uses env x) (mergeLeft fcs fd),
            (Data.Builder.piece px, (n, LocatedIR.Terminator.Switch rx (zip keys labels) ld)))
      where
        ||| A switch's cases, each a block of its own, in order.
        cases : All (\_ => TermIR.Body d c m ls ctx) ks -> Data.RAList (HV enc) ctx ->
                Data.RAList (LI enc) ls ->
                M enc (RegMap enc, List LocatedIR.Label)
        cases [] env li = pure (empty, [])
        cases (b :: bs) env li = do
          (fb, l) <- branchTo b env li
          (fbs, ls) <- cases bs env li
          pure (mergeLeft fb fbs, l :: ls)
    body (TermIR.Body.Call f xs k) env li = do
      n <- freshDefs 1
      lr <- freshLabel
      r <- fresh IRCommon.Ty.Val
      (fk, codeK) <- body k (InReg n r :: env) li
      let outer = without [LocatedIR.Location.At r] fk
          live = places outer
      addBlock lr (live ++ [LocatedIR.Location.At r])
        (values outer ++ [(LocatedIR.Content.Value n, LocatedIR.Location.At r)]) codeK
      pure (mergeLeft (usesAll env xs) outer,
            (neutral,
              (n,
                LocatedIR.Terminator.Call (varName f) (operands env xs)
                (LocatedIR.MkCont lr live))))
    body (TermIR.Body.TailCall f xs) env li = do
      n <- freshDefs 1
      pure (usesAll env xs,
            (neutral, (n, LocatedIR.Terminator.TailCall (varName f) (operands env xs))))
    body (TermIR.Body.Apply f x k) env li = do
      n <- freshDefs 1
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      lr <- freshLabel
      r <- fresh IRCommon.Ty.Val
      (fk, codeK) <- body k (InReg n r :: env) li
      let outer = without [LocatedIR.Location.At r] fk
          live = places outer
      addBlock lr (live ++ [LocatedIR.Location.At r])
        (values outer ++ [(LocatedIR.Content.Value n, LocatedIR.Location.At r)]) codeK
      pure (mergeLeft (mergeLeft (uses env f) (uses env x)) outer,
            (Data.Builder.piece (pf ++ px),
              (n, LocatedIR.Terminator.Apply rf rx (LocatedIR.MkCont lr live))))
    body (TermIR.Body.TailApply f x) env li = do
      n <- freshDefs 1
      (pf, rf) <- asReg env f
      (px, rx) <- asReg env x
      pure (mergeLeft (uses env f) (uses env x),
            (Data.Builder.piece (pf ++ px), (n, LocatedIR.Terminator.TailApply rf rx)))
    body (TermIR.Body.Return x) env li = do
      n <- freshDefs 1
      pure (uses env x, (neutral, (n, LocatedIR.Terminator.Return (operand env x))))
    body (TermIR.Body.Enter f xs) env li = do
      n <- freshDefs 1
      (pf, rf) <- asReg env f
      pure (mergeLeft (uses env f) (usesList env xs),
            (Data.Builder.piece pf, (n, LocatedIR.Terminator.Enter rf (map (operand env) xs))))
      where
        usesList : Data.RAList (HV enc) ctx -> List (TermIR.Opnd (TermIR.Var ctx) t) -> RegMap enc
        usesList env = foldr (\x, m => mergeLeft (uses env x) m) empty
    body (TermIR.Body.Ret xs) env li = do
      n <- freshDefs 1
      pure (usesAll env xs, (neutral, (n, LocatedIR.Terminator.Ret (operands env xs))))
    body (TermIR.Body.Crash s) env li = do
      n <- freshDefs 1
      pure (empty, (neutral, (n, LocatedIR.Terminator.Crash s)))
    body (TermIR.Body.Unsupported s) env li = do
      n <- freshDefs 1
      pure (empty, (neutral, (n, LocatedIR.Terminator.Unsupported s)))

    ||| An instruction's registers, bound in the environment of the rest.
    bind : (ts : List (IRCommon.Ty enc)) -> TermIR.Instr d m (TermIR.Var ctx) ts ->
           TermIR.Body d c m ls (ts ++ ctx) ->
           Data.RAList (HV enc) ctx -> Data.RAList (LI enc) ls -> M enc (Lowered enc)
    bind ts i k env li = do
      def <- freshDefs (max 1 (length ts))
      ds <- results ts i
      (after, (is, t)) <- body k (Data.RAList.prepend (held def ds) env) li
      let outer = without (regs ds) after
      pre <- instr def env ds outer i
      pure (mergeLeft (instrUses env i) outer, (Data.Builder.piece pre <+> is, t))
      where
        ||| The variable's register under the type, or a fresh one if it has
        ||| none.
        retyped : (t : IRCommon.Ty enc) -> TermIR.Var ctx s -> M enc (All (RV enc) [t])
        retyped t x = case TermIR.Var.fetch x env of
          InReg _ r => pure [LocatedIR.Location.Slot (number (LocatedIR.Location.At r)) t]
          OfStatic _ _ => freshAll [t]

        ||| The registers an instruction binds: fresh ones, but for a retyping
        ||| of a register, which binds that register under the new type, as
        ||| both are raw words.
        results : (ts' : List (IRCommon.Ty enc)) -> TermIR.Instr d m (TermIR.Var ctx) ts' ->
                  M enc (All (RV enc) ts')
        results _ (TermIR.Instr.ByteAddrToWord (TermIR.Opnd.V x)) = retyped IRCommon.Ty.W64 x
        results _ (TermIR.Instr.WordToByteAddr (TermIR.Opnd.V x)) = retyped IRCommon.Ty.ByteAddr x
        results ts' _ = freshAll ts'

        ||| The registers of the environment an instruction reads.
        instrUses : Data.RAList (HV enc) ctx -> TermIR.Instr d m (TermIR.Var ctx) ts -> RegMap enc
        instrUses env i =
          fst
            (Data.Stateful.toPair
             (Data.Stateful.outcome empty (TermIR.Instr.traverseInstr (collect env) i)))
          where
            collect : Data.RAList (HV enc) ctx -> {0 t : IRCommon.Ty enc} ->
                      TermIR.Opnd (TermIR.Var ctx) t ->
                      Data.Stateful (RegMap enc) Void (TermIR.Opnd (TermIR.Var ctx) t)
            collect env x = do Data.Stateful.modify (mergeLeft (uses env x)); pure x

        ||| The steps of an instruction binding the registers `ds`, given what is
        ||| live after it: the operation of number `def` and the shuffles that
        ||| put its immediate operands into registers.
        instr : (def : Nat) -> Data.RAList (HV enc) ctx''' -> All (RV enc) ts' ->
                (after : RegMap enc) -> TermIR.Instr d m' (TermIR.Var ctx''') ts' ->
                M enc (List (LocatedIR.Step enc))
        instr def env z after instr' = case (z, instr') of
          ([r], TermIR.Instr.FConst x) => pure [LocatedIR.Step.Op def (LocatedIR.Instr.FConst r x)]
          ([r], TermIR.Instr.CodeOf f) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.CodeOf r (varName f))]
          -- not reached: `body` holds a static's address as itself, in no register
          ([r], TermIR.Instr.StaticAddr s) =>
            pure [remat r (LocatedIR.Step.StaticAddress (varSym s))]
          ([r], TermIR.Instr.AreaAddr a) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.AreaAddr r a)]
          ([r], TermIR.Instr.Offset a n) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.Offset r (operand env a) (operand env n))]
          ([r], TermIR.Instr.Arith o x y) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.Arith o r (operand env x) (operand env y))]
          ([h, l], TermIR.Instr.Mul128 x y) =>
            pure
              [LocatedIR.Step.Op def (LocatedIR.Instr.Mul128 h l (operand env x) (operand env y))]
          ([q, r], TermIR.Instr.Div128 h l x) =>
            pure
              [LocatedIR.Step.Op def
               (LocatedIR.Instr.Div128 q r (operand env h) (operand env l) (operand env x))]
          ([r], TermIR.Instr.Unary o x) => unary env x (LocatedIR.Instr.Unary o r)
          ([r], TermIR.Instr.Ext w s x) => unary env x (LocatedIR.Instr.Ext w s r)
          ([r], TermIR.Instr.FArith o x y) => binary env x y (LocatedIR.Instr.FArith o r)
          ([r], TermIR.Instr.FNeg x) => unary env x (LocatedIR.Instr.FNeg r)
          ([r], TermIR.Instr.FSqrt x) => unary env x (LocatedIR.Instr.FSqrt r)
          ([r], TermIR.Instr.FCmp rel x y) => binary env x y (LocatedIR.Instr.FCmp rel r)
          ([r], TermIR.Instr.Convert op x) => unary env x (LocatedIR.Instr.Convert op r)
          ([r], TermIR.Instr.Cmp rel x y) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.Cmp rel r (operand env x) (operand env y))]
          ([r], TermIR.Instr.Load t mem) => do (p, m') <- memRef env mem
                                               pure
                                                 (p
                                                   ++
                                                     [LocatedIR.Step.Op def
                                                      (LocatedIR.Instr.Load t r m')])
          ([], TermIR.Instr.Store t mem x) => do
            (p, m') <- memRef env mem
            (px, rx) <- asReg env x
            pure (p ++ px ++ [LocatedIR.Step.Op def (LocatedIR.Instr.Store t m' rx)])
          ([r], TermIR.Instr.LoadN w s mem) => do (p, m') <- memRef env mem
                                                  pure
                                                    (p
                                                      ++
                                                        [LocatedIR.Step.Op def
                                                         (LocatedIR.Instr.LoadN w s r m')])
          ([], TermIR.Instr.StoreN w mem x) => do
            (p, m') <- memRef env mem
            (px, rx) <- asReg env x
            pure (p ++ px ++ [LocatedIR.Step.Op def (LocatedIR.Instr.StoreN w m' rx)])
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
          -- a retyping of a register is the register (`results`); of a word,
          -- the word in the result's
          ([r], TermIR.Instr.ByteAddrToWord (TermIR.Opnd.V x)) => retyping x r
          ([r], TermIR.Instr.WordToByteAddr (TermIR.Opnd.V x)) => retyping x r
          ([r], TermIR.Instr.WordToByteAddr (TermIR.Opnd.W w)) => pure [immediate r w]
          ([r], TermIR.Instr.LoadHeader x) => unary env x (LocatedIR.Instr.LoadHeader r)
          ([r], TermIR.Instr.LoadPart p x) => unary env x (LocatedIR.Instr.LoadPart p r)
          ([r], TermIR.Instr.AllocObj h fs) =>
            -- the fields are written after the slow path's collection; an
            -- object of a fixed size up to the margin is a bump past a check
            -- of its own, any other checks for itself
            let live = places (mergeLeft after (usesAll env fs))
                made = LocatedIR.Instr.AllocObj r h (operands env fs)
            in pure (if LocatedIR.Instr.afterCheck h
                       then [ LocatedIR.Step.Check (8 * Types.Header.objectWords h) live
                            , LocatedIR.Step.Op def (made Nothing) ]
                       else [LocatedIR.Step.Op def (made (Just live))])
          ([r], TermIR.Instr.AllocSized p n f) => do
            (pn, rn) <- asReg env n
            let fill = fillOperand p f
                live =
                  places
                    (mergeLeft after
                     (mergeLeft
                        (singleton (number (LocatedIR.Location.At rn))
                          (content env n, LocatedIR.Location.At rn))
                        (maybe empty (fillUses p f) (Just ()))))
            pure (pn ++ [LocatedIR.Step.Op def (LocatedIR.Instr.AllocSized r p rn fill live)])
          (ds, TermIR.Instr.DirectCall f xs) =>
            pure
              [LocatedIR.Step.Op def
                (LocatedIR.Instr.DirectCall (varName f) (operands env xs) (regs ds) (isCollecting f)
               (places after))]
          ([d], TermIR.Instr.GetPinned r) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.GetPinned r d)]
          ([], TermIR.Instr.SetPinned r x) =>
            pure [LocatedIR.Step.Op def (LocatedIR.Instr.SetPinned r (operand env x))]
          ([d], TermIR.Instr.SystemCall n xs) =>
            pure
              [LocatedIR.Step.Op def
               (LocatedIR.Instr.SystemCall d (wordOperands env {k = S (finToNat n)} xs))]
          ([], TermIR.Instr.Loc fc) => pure [LocatedIR.Step.Op def (LocatedIR.Instr.Loc fc)]
          ([], TermIR.Instr.Comment s) => pure [LocatedIR.Step.Op def (LocatedIR.Instr.Comment s)]
          where
            fillOperand : {0 kind : Types.Kind} -> (q : Types.Header.HeaderPart kind) ->
                          TermIR.Sizes.Fill (TermIR.Var ctx''') q ->
                          Maybe (LocatedIR.Opnd enc IRCommon.Ty.Val)
            fillOperand Types.Header.ArrayElemsP x = Just (operand env x)
            fillOperand _ _ = Nothing
            fillUses : {0 kind : Types.Kind} -> (q : Types.Header.HeaderPart kind) ->
                       TermIR.Sizes.Fill (TermIR.Var ctx''') q -> () -> RegMap enc
            fillUses Types.Header.ArrayElemsP x _ = uses env x
            fillUses _ _ _ = empty

            isCollecting : TermIR.Var d.sigs s -> Bool
            isCollecting r = case (TermIR.Var.entry declared.sigs r).conv of
              IRCommon.Conv.CPS => False
              IRCommon.Conv.Direct _ col => col

            memRef : Data.RAList (HV enc'') ctx'' -> TermIR.Mem (TermIR.Var ctx'') cell ->
                     M enc'' (List (LocatedIR.Step enc''), LocatedIR.Mem enc'')
            memRef env (TermIR.MkMem b i o) = do
              (pb, rb) <- baseReg env b
              case i of
                Nothing => pure (pb, LocatedIR.MkMem rb Nothing o)
                Just x => do (pi, ri) <- asReg env x
                             pure (pb ++ pi, LocatedIR.MkMem rb (Just ri) o)
              where
                baseReg : Data.RAList (HV enc') ctx' -> TermIR.Mem.Base (TermIR.Var ctx') b' ->
                          M enc' (List (LocatedIR.Step enc'), LocatedIR.Mem.Base enc')
                baseReg env (TermIR.Mem.AtBytes x) = do (p, r) <- asReg env x
                                                        pure (p, LocatedIR.Mem.AtBytes r)
                baseReg env (TermIR.Mem.AtPtr x) = do (p, r) <- asReg env x
                                                      pure (p, LocatedIR.Mem.AtPtr r)

            ||| A retyping of a variable: nothing if it is in a register, which
            ||| the result is already; a static's address put in the result.
            retyping : TermIR.Var ctx''' s -> LocatedIR.Location enc u ->
                       M enc (List (LocatedIR.Step enc))
            retyping x r = case TermIR.Var.fetch x env of
              InReg _ _ => pure []
              OfStatic n _ => pure [remat r (LocatedIR.Step.StaticAddress n)]

            ||| One register, through an instruction that reads it from an operand.
            unary : Data.RAList (HV enc) ctx' -> TermIR.Opnd (TermIR.Var ctx') t ->
                    (LocatedIR.Location enc t -> LocatedIR.Instr enc) ->
                    M enc (List (LocatedIR.Step enc))
            unary env x f = do (p, r) <- asReg env x; pure (p ++ [LocatedIR.Step.Op def (f r)])

            binary : Data.RAList (HV enc) ctx' -> TermIR.Opnd (TermIR.Var ctx') t ->
                     TermIR.Opnd (TermIR.Var ctx') u ->
                     (LocatedIR.Location enc t -> LocatedIR.Location enc u ->
                      LocatedIR.Instr enc) ->
                     M enc (List (LocatedIR.Step enc))
            binary env x y f = do (px, rx) <- asReg env x
                                  (py, ry) <- asReg env y
                                  pure (px ++ py ++ [LocatedIR.Step.Op def (f rx ry)])

  functions : (ss : List (TermIR.Sig enc)) -> All (TermIR.Def d) ss -> List (LocatedIR.Function enc)
  functions [] [] = []
  functions (s :: ss) (TermIR.Def.Defined b :: ds) = function s b :: functions ss ds
    where
      function : (s : TermIR.Sig enc) -> TermIR.Body d s.conv s.converts [] s.params ->
                 LocatedIR.Function enc
      function s b =
        let run : M enc (List (LocatedIR.Location.Place enc))
            run = do
              ps <- freshAll s.params
              first <- freshDefs (length s.params)
              Data.Stateful.modify { joins := snd (frees b (length s.params) 0 []) [] }
              (_, code) <- body b (Data.RAList.fromAll (held first ps)) []
              addBlock 0 [] (entries first ps) code
              pure (regs ps)
        in case Data.Stateful.toPair (Data.Stateful.outcome (MkSt 0 0 1 empty []) run) of
             (st, ps) => LocatedIR.MkFunction s.name s.conv ps 0 (values st.blocks) EmptyFC
        where
          ||| The levels a body reads of the variables bound outside it, directly or
          ||| through the blocks it jumps to (`lf` is what each of the `labels`
          ||| labels in scope reads); and what each join's block reads, in the order
          ||| the lowering meets the joins: a join, then those in the code that
          ||| reaches it, then those in its block. A join's block is computed with
          ||| its own label reading only itself (`Right`), the least fixed point;
          ||| if the block reaches the label, a loop, every join inside it whose set
          ||| reaches the label reads the block's set too, which is known once the
          ||| block is done. Once for a whole body: computing a block's at its join read
          ||| the rest of the function again at every join, the square of its length.
          ||| `union s t` inserts each level of `t` into `s`, so what the code after a
          ||| binder or a branch reads, which can be most of the function's levels,
          ||| comes first, and a node's own few levels second: the other way, a body
          ||| that keeps many levels in use paid for all of them at every binder.
          frees : TermIR.Body d'' c m ls ctx -> (depth, labels : Nat) ->
                  Data.RAList (\_ => SortedSet Read) ls ->
                  (SortedSet Read, List JoinFrees -> List JoinFrees)
          frees body' depth labels lf = case body' of
            TermIR.Body.Bind {ts} i k =>
                          let (fk, jk) = frees k (depth + length ts) labels lf
                          in (union (outside depth (length ts) fk) (instrLevels depth i), jk)
            TermIR.Body.Join ps b r =>
                          let self = Right labels
                              (fb, jb) =
                                frees b (depth + length ps) (S labels) (singleton self :: lf)
                              block = delete self (outside depth (length ps) fb)
                              (fr, jr) = frees r depth (S labels) (block :: lf)
                              inner = if contains self fb
                                         then (map (completed self block) (jb []) ++)
                                         else jb
                          in (fr, \rest => (depth, block) :: jr (inner rest))
            TermIR.Body.Jump l xs => (union (TermIR.Var.fetch l lf) (opsLevels depth xs), id)
            TermIR.Body.Branch _ x y a b =>
              let (fa, ja) = frees a depth labels lf
                  (fb, jb) = frees b depth labels lf
              in (union (union fb fa) (union (opLevel depth x) (opLevel depth y)), ja . jb)
            TermIR.Body.IfFixnums {n} vs y no =>
              let (fy, jy) = frees y (depth + S n) labels lf
                  (fn, jn) = frees no depth labels lf
              in (union (union (outside depth (S n) fy) fn) (vectLevels depth vs), jy . jn)
            TermIR.Body.ArithOv _ x y ok ovf =>
              let (fo, jo) = frees ok (S depth) labels lf
                  (fv, jv) = frees ovf depth labels lf
              in (union (union (outside depth 1 fo) fv) (union (opLevel depth x) (opLevel depth y)),
                  jo . jv)
            TermIR.Body.TagOv x ok ovf =>
              let (fo, jo) = frees ok (S depth) labels lf
                  (fv, jv) = frees ovf depth labels lf
              in (union (union (outside depth 1 fo) fv) (opLevel depth x), jo . jv)
            TermIR.Body.Switch x _ bs dflt =>
              let (fc, jc) = freesCases bs depth labels lf
                  (fd, jd) = frees dflt depth labels lf
              in (union (union fd fc) (opLevel depth x), jc . jd)
            TermIR.Body.Call _ xs k =>
              let (fk, jk) =
                    frees k (S depth) labels lf in
                      (union (outside depth 1 fk) (opsLevels depth xs), jk)
            TermIR.Body.TailCall _ xs => (opsLevels depth xs, id)
            TermIR.Body.Apply f x k =>
              let (fk, jk) = frees k (S depth) labels lf
              in (union (outside depth 1 fk) (union (opLevel depth f) (opLevel depth x)), jk)
            TermIR.Body.TailApply f x => (union (opLevel depth f) (opLevel depth x), id)
            TermIR.Body.Return x => (opLevel depth x, id)
            TermIR.Body.Enter f xs => (union (listLevels depth xs) (opLevel depth f), id)
            TermIR.Body.Ret xs => (opsLevels depth xs, id)
            TermIR.Body.Crash _ => (empty, id)
            TermIR.Body.Unsupported _ => (empty, id)
            where
              opLevel : (depth : Nat) -> TermIR.Opnd (TermIR.Var ctx'') t -> SortedSet Read
              opLevel depth (TermIR.Opnd.V x) = singleton (Left (Data.Level.level depth x.index))
              opLevel _ _ = empty

              ||| The levels an instruction reads.
              instrLevels : (depth : Nat) -> TermIR.Instr d' m' (TermIR.Var ctx') ts' ->
                            SortedSet Read
              instrLevels depth i =
                fst (Data.Stateful.toPair (Data.Stateful.outcome empty
                  (TermIR.Instr.traverseInstr (\x => do Data.Stateful.modify
                                                          (\s => union s (opLevel depth x))
                                                        pure x) i)))

              vectLevels : (depth : Nat) -> Vect n' (TermIR.Opnd (TermIR.Var ctx) t) ->
                           SortedSet Read
              vectLevels depth = foldr (\x, s => union s (opLevel depth x)) empty

              freesCases : All (\_ => TermIR.Body d' c' m' ls' ctx') ks -> (depth, labels : Nat) ->
                           Data.RAList (\_ => SortedSet Read) ls' ->
                           (SortedSet Read, List JoinFrees -> List JoinFrees)
              freesCases [] depth labels lf = (empty, id)
              freesCases (b :: bs) depth labels lf =
                let (fb, jb) = frees b depth labels lf
                    (fs, js) = freesCases bs depth labels lf
                in (union fs fb, jb . js)

              listLevels : (depth : Nat) -> List (TermIR.Opnd (TermIR.Var ctx) t) -> SortedSet Read
              listLevels depth = foldr (\x, s => union s (opLevel depth x)) empty

              opsLevels : (depth : Nat) -> All (TermIR.Opnd (TermIR.Var ctx)) ts -> SortedSet Read
              opsLevels depth [] = empty
              opsLevels depth (x :: xs) = union (opsLevels depth xs) (opLevel depth x)

              ||| The levels of a body's own first `n` binders, from `depth`, taken out of
              ||| what it reads: what is left, it reads from outside.
              outside : (depth : Nat) -> (n : Nat) -> SortedSet Read -> SortedSet Read
              outside depth Z s = s
              outside depth (S n) s = outside (S depth) n (delete (Left depth) s)

              ||| A join's set inside a loop's block, completed once the loop's
              ||| block's is known: a join that reaches the loop reads what the
              ||| loop's block reads.
              completed : Read -> SortedSet Read -> JoinFrees -> JoinFrees
              completed self block (d, s) =
                if contains self s then (d, union (delete self s) block) else (d, s)
  functions (_ :: ss) (TermIR.Def.External :: ds) = functions ss ds

  statics : (ss : List TermIR.StaticSig) -> All (TermIR.StaticDef d) ss ->
            List (LocatedIR.Static enc)
  statics [] [] = []
  statics (TermIR.MkStaticSig sym k :: ss) (TermIR.MkStaticDef h fs :: ds) =
    LocatedIR.MkStatic sym k h (fields fs) :: statics ss ds
    where
      field : TermIR.StaticDef.SField d t -> LocatedIR.Static.SField
      field (TermIR.StaticDef.SWord w) = LocatedIR.Static.SWord w
      field (TermIR.StaticDef.SVal i) = LocatedIR.Static.SVal i
      field (TermIR.StaticDef.SRef s) = LocatedIR.Static.SRef (varSym s)
      field (TermIR.StaticDef.SCode f) = LocatedIR.Static.SCode (varName f)

      -- each field's located word, in order
      fields : All (TermIR.StaticDef.SField d) ts -> List LocatedIR.Static.SField
      fields [] = []
      fields (f :: fs') = field f :: fields fs'

  entryName : TermIR.Program.Entry d -> Name
  entryName (TermIR.Program.MkEntry f) = varName f

||| The IR's programs, for producers that build terms and need not import
||| the IR, whose names the term's share.
export
0 LocatedProgram : Types.Enc -> Type
LocatedProgram enc = LocatedIR.Program enc

||| The program in the IR, for the target.
export
allocRegs : {enc : Types.Enc} -> {d : TermIR.Decls enc} -> Target -> TermIR.Program enc d ->
            LocatedIR.Program enc
allocRegs target (TermIR.MkProgram fs ss e conIds) =
  let declared = MkDeclared (Data.RAList.fromList d.sigs) (Data.RAList.fromList d.statics)
  in LocatedIR.MkProgram target (functions declared d.sigs fs) (statics declared d.statics ss)
       (entryName declared e) conIds
