||| How producers build the term IR (`Native.Codegen.TermIR.Program`).
|||
||| A producer writes a body in PHOAS: a binder is an Idris function over an
||| abstract type of variables `v` (and of labels `l`), so Idris checks the
||| producer's scoping and types when the producer is compiled. A
||| continuation monad over these bodies, `Build`, keeps producer code
||| direct-style: the rest of a `do` block is the body under a binder, a
||| call's continuation, or a join point's block. Nothing is numbered by
||| hand, and no live list is written.
|||
||| `close` turns a closed body into the term once, by instantiating `v` and
||| `l` with levels and computing each variable's position. A level that
||| does not match its context cannot occur in a body built parametrically,
||| and every closed body is, since `v` and `l` are erased; `close` still
||| has to say what it does then, which is to return `Nothing`.
module Native.Codegen.TermIR.Build

import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.OvOp
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.Var

import Core.Name
import Data.List
import Data.List.Quantifiers
import Data.Singleton
import Data.So
import Data.Vect
import Decidable.Equality
import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Data.Distinct
import Native.Data.RAList as Data
import Native.HeapObj.ValEnc
import Native.Types.Enc as Types

%default total

------------------------------------------------------------------------------
-- Bodies with binders

||| A body whose binders are functions, mirroring `Body`.
export
data PBody : Decls enc -> IRCommon.Conv enc -> Bool -> (v : IRCommon.Ty enc -> Type) ->
  (l : List (IRCommon.Ty enc) -> Type) -> Type where
  PBind : {ts : List (IRCommon.Ty enc)} -> Instr d m v ts -> (All v ts -> PBody d c m v l) ->
          PBody d c m v l
  PJoin : (ps : List (IRCommon.Ty enc)) -> (l ps -> All v ps -> PBody d c m v l) ->
          (l ps -> PBody d c m v l) ->
          PBody d c m v l
  PJump : l ps -> All (Opnd v) ps -> PBody d c m v l
  PBranch : {auto 0 int : IsInt t} -> IRCommon.Op.Rel -> Opnd v t -> Opnd v t ->
            (yes, no : PBody d c m v l) ->
            PBody d c m v l
  PIfFixnums : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
               {n : Nat} -> Vect (S n) (Opnd v IRCommon.Ty.Val) ->
               (All v (replicate (S n) (IRCommon.Ty.Fix {enc})) -> PBody d c m v l) ->
               PBody d c m v l ->
               PBody d c m v l
  PArithOv : {t : IRCommon.Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Opnd v t -> Opnd v t ->
             (v t -> PBody d c m v l) -> PBody d c m v l -> PBody d c m v l
  PTagOv : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} ->
           Opnd v IRCommon.Ty.W64 -> (v (IRCommon.Ty.Fix {enc}) -> PBody d c m v l) ->
           PBody d c m v l ->
           PBody d c m v l
  PSwitch : {auto 0 int : IsInt t} -> Opnd v t -> (keys : List Int64) ->
            {auto 0 ok : So (distinct keys && keysFit t keys)} ->
            All (\_ => PBody d c m v l) keys -> PBody d c m v l -> PBody d c m v l
  PCall : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> All (Opnd v) ps ->
          (v IRCommon.Ty.Val -> PBody d IRCommon.Conv.CPS m v l) ->
          PBody d IRCommon.Conv.CPS m v l
  PTailCall : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> All (Opnd v) ps ->
              PBody d IRCommon.Conv.CPS m v l
  PApply : (fn, arg : Opnd v IRCommon.Ty.Val) ->
           (v IRCommon.Ty.Val -> PBody d IRCommon.Conv.CPS m v l) ->
           PBody d IRCommon.Conv.CPS m v l
  PTailApply : (fn, arg : Opnd v IRCommon.Ty.Val) -> PBody d IRCommon.Conv.CPS m v l
  PReturn : Opnd v IRCommon.Ty.Val -> PBody d IRCommon.Conv.CPS m v l
  PEnter : Opnd v IRCommon.Ty.CodeAddr -> List (Opnd v IRCommon.Ty.Val) -> PBody d c m v l
  PRet : All (Opnd v) rs -> PBody d (IRCommon.Conv.Direct rs col) m v l
  PCrash : String -> PBody d c m v l
  PUnsupported : String -> PBody d c m v l

||| A closed body over parameters of the types: parametric in its
||| variables and labels.
public export
0 Closed : Decls enc -> IRCommon.Conv enc -> Bool -> List (IRCommon.Ty enc) -> Type
Closed d c m ps = {0 v : IRCommon.Ty enc -> Type} -> {0 l : List (IRCommon.Ty enc) -> Type} ->
  All v ps ->
  PBody d c m v l

------------------------------------------------------------------------------
-- `Build`

||| Code that, given the rest of the body, makes the body.
public export
record Build (d : Decls enc) (c : IRCommon.Conv enc) (m : Bool) (v : IRCommon.Ty enc -> Type)
  (l : List (IRCommon.Ty enc) -> Type) (a : Type) where
  constructor MkBuild
  run : (a -> PBody d c m v l) -> PBody d c m v l

export
Functor (Build d c m v l) where
  map f b = MkBuild (\k => b.run (k . f))

export
Applicative (Build d c m v l) where
  pure x = MkBuild (\k => k x)
  bf <*> bx = MkBuild (\k => bf.run (\f => bx.run (k . f)))

export
Monad (Build d c m v l) where
  b >>= f = MkBuild (\k => b.run (\x => (f x).run k))

||| Code that ends the body: it never reaches the rest.
public export
0 End : Decls enc -> IRCommon.Conv enc -> Bool -> (IRCommon.Ty enc -> Type) ->
        (List (IRCommon.Ty enc) -> Type) -> Type
End d c m v l = Build d c m v l Void

||| The body that code ending in a terminator makes.
export
finish : End d c m v l -> PBody d c m v l
finish b = b.run absurd

vars : All v qs -> All (Opnd v) qs
vars [] = []
vars (x :: xs) = Opnd.V x :: vars xs

||| A body from `Build` code over the parameters.
export
build : ({0 v : IRCommon.Ty enc -> Type} -> {0 l : List (IRCommon.Ty enc) -> Type} ->
         All (Opnd v) ps ->
         End d c m v l) ->
        Closed d c m ps
build f xs = finish (f (vars xs))

||| An instruction, binding its results.
export
emit : {ts : List (IRCommon.Ty enc)} -> Instr d m v ts -> Build d c m v l (All v ts)
emit i = MkBuild (PBind i)

||| An instruction of one result.
export
emit1 : {t : IRCommon.Ty enc} -> Instr d m v [t] -> Build d c m v l (Opnd v t)
emit1 i = MkBuild (\k => PBind i (\[x] => k (Opnd.V x)))

||| An instruction of no result.
export
emit0 : Instr d m v [] -> Build d c m v l ()
emit0 i = MkBuild (\k => PBind i (\[] => k ()))

||| A Direct call, binding its results.
export
directCall : {rs : List (IRCommon.Ty enc)} ->
             Var d.sigs (MkSig n (IRCommon.Conv.Direct rs col) ps cv) ->
             All (Opnd v) ps ->
             Build d c m v l (All (Opnd v) rs)
directCall f xs = vars <$> emit (Instr.DirectCall f xs)

||| A CPS call: the rest of the code is its continuation.
export
call : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> All (Opnd v) ps ->
       Build d IRCommon.Conv.CPS m v l (Opnd v IRCommon.Ty.Val)
call f xs = MkBuild (\k => PCall f xs (k . Opnd.V))

||| A closure applied to one argument: the rest of the code is its
||| continuation.
export
apply : (fn, arg : Opnd v IRCommon.Ty.Val) ->
        Build d IRCommon.Conv.CPS m v l (Opnd v IRCommon.Ty.Val)
apply f x = MkBuild (\k => PApply f x (k . Opnd.V))

export
tailCall : Var d.sigs (MkSig n IRCommon.Conv.CPS ps cv) -> All (Opnd v) ps ->
           End d IRCommon.Conv.CPS m v l
tailCall f xs = MkBuild (\_ => PTailCall f xs)

export
tailApply : (fn, arg : Opnd v IRCommon.Ty.Val) -> End d IRCommon.Conv.CPS m v l
tailApply f x = MkBuild (\_ => PTailApply f x)

export
return : Opnd v IRCommon.Ty.Val -> End d IRCommon.Conv.CPS m v l
return x = MkBuild (\_ => PReturn x)

export
ret : All (Opnd v) rs -> End d (IRCommon.Conv.Direct rs col) m v l
ret xs = MkBuild (\_ => PRet xs)

export
enter : Opnd v IRCommon.Ty.CodeAddr -> List (Opnd v IRCommon.Ty.Val) -> End d c m v l
enter f xs = MkBuild (\_ => PEnter f xs)

||| End the body with a crash, whatever the rest would have been.
export
crash : String -> Build d c m v l a
crash s = MkBuild (\_ => PCrash s)

||| End the body with the abort stub, for a construct not lowered yet.
export
unsupported : String -> Build d c m v l a
unsupported s = MkBuild (\_ => PUnsupported s)

||| A jump to a block with its parameters.
public export
0 Jumper : Decls enc -> IRCommon.Conv enc -> Bool -> (IRCommon.Ty enc -> Type) ->
           (List (IRCommon.Ty enc) -> Type) ->
           List (IRCommon.Ty enc) -> Type
Jumper d c m v l ps = All (Opnd v) ps -> End d c m v l

jumpTo : l ps -> Jumper d c m v l ps
jumpTo lbl xs = MkBuild (\_ => PJump lbl xs)

||| A block with parameters, which the rest of the code may jump to.
export
block : (ps : List (IRCommon.Ty enc)) -> (All (Opnd v) ps -> End d c m v l) ->
        Build d c m v l (Jumper d c m v l ps)
block ps body =
  MkBuild (\k => PJoin ps (\_, xs => finish (body (vars xs))) (\lbl => k (jumpTo lbl)))

||| A join: the code given ends by jumping to the exit with values, and the
||| rest of the code runs on them, lowered once.
export
joinPoint : (ps : List (IRCommon.Ty enc)) -> (Jumper d c m v l ps -> End d c m v l) ->
            Build d c m v l (All (Opnd v) ps)
joinPoint ps f = MkBuild (\k => PJoin ps (\_, xs => k (vars xs)) (\lbl => finish (f (jumpTo lbl))))

||| A loop: the body runs on the initial values and may jump back with new
||| ones. It leaves only through an enclosing join or a terminator.
export
loop : (ps : List (IRCommon.Ty enc)) -> All (Opnd v) ps ->
       (Jumper d c m v l ps -> All (Opnd v) ps -> End d c m v l) -> End d c m v l
loop ps init body =
  MkBuild
    (\_ => PJoin ps (\lbl, xs => finish (body (jumpTo lbl) (vars xs))) (\lbl => PJump lbl init))

||| Compare two integers and branch.
export
branch : {auto 0 int : IsInt t} -> IRCommon.Op.Rel -> Opnd v t -> Opnd v t ->
         (yes, no : End d c m v l) -> End d c m v l
branch r x y yes no = MkBuild (\_ => PBranch r x y (finish yes) (finish no))

||| Leave by the code given when the relation holds; else go on.
export
leaveIf : {auto 0 int : IsInt t} -> IRCommon.Op.Rel -> Opnd v t -> Opnd v t -> End d c m v l ->
          Build d c m v l ()
leaveIf r x y out = MkBuild (\k => PBranch r x y (finish out) (k ()))

||| Whether every value is a fixnum; the yes branch has them as `Fix`es.
||| An immediate is a fixnum (the erased value is fixnum 0), so only the
||| variables are tested, and with none the yes branch is taken outright.
export
ifFixnums : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> {n : Nat} ->
            Vect (S n) (Opnd v IRCommon.Ty.Val) ->
            (All (Opnd v) (replicate (S n) (IRCommon.Ty.Fix {enc})) -> End d c m v l) ->
            End d c m v l -> End d c m v l
ifFixnums vs yes no = case variables vs of
    [] => yes (fixes (fill vs []))
    (t :: ts) => MkBuild (\_ => PIfFixnums (Opnd.V t :: map Opnd.V (fromList ts))
                                   (\fs =>
                                     finish
                                     (yes (fixes (fill vs (narrowed {k = S (length ts)} fs)))))
                                   (finish no))
  where
    -- The values to test: the variables.
    variables : Vect j (Opnd v IRCommon.Ty.Val) -> List (v IRCommon.Ty.Val)
    variables [] = []
    variables (Opnd.V x :: xs) = x :: variables xs
    variables (_ :: xs) = variables xs

    -- The tested values, narrowed, in order.
    narrowed : {k : Nat} -> All v (replicate k (IRCommon.Ty.Fix {enc})) ->
               List (v (IRCommon.Ty.Fix {enc}))
    narrowed {k = Z} [] = []
    narrowed {k = S k} (f :: fs) = f :: narrowed fs

    -- Each value as a `Fix`: an immediate as itself, a variable as the next
    -- narrowed one.
    fill : Vect j (Opnd v IRCommon.Ty.Val) -> List (v (IRCommon.Ty.Fix {enc})) ->
           Vect j (Opnd v (IRCommon.Ty.Fix {enc}))
    fill [] _ = []
    fill (Opnd.Vx {ok} i :: xs) fs = Opnd.Fx {ok} i :: fill xs fs
    fill (Opnd.Erased :: xs) fs = Opnd.Fx 0 :: fill xs fs
    fill (Opnd.V _ :: xs) (f :: fs) = Opnd.V f :: fill xs fs
    fill (Opnd.V _ :: xs) [] = Opnd.Fx 0
      :: fill xs []   -- not reached: one narrowed value per variable

    fixes : Vect j (Opnd v (IRCommon.Ty.Fix {enc})) ->
            All (Opnd v) (replicate j (IRCommon.Ty.Fix {enc}))
    fixes [] = []
    fixes (x :: xs) = x :: fixes xs

||| Arithmetic with its overflow branch.
export
arithOv : {t : IRCommon.Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Opnd v t -> Opnd v t ->
          (Opnd v t -> End d c m v l) -> End d c m v l -> End d c m v l
arithOv o x y ok ovf = MkBuild (\_ => PArithOv o x y (finish . ok . Opnd.V) (finish ovf))

||| The fixnum of a word, with the branch for a word out of range.
export
tagOv : {auto 0 fx : HeapObj.ValEnc.HasFixnums enc.val} -> Opnd v IRCommon.Ty.W64 ->
        (Opnd v (IRCommon.Ty.Fix {enc}) -> End d c m v l) -> End d c m v l -> End d c m v l
tagOv x ok ovf = MkBuild (\_ => PTagOv x (finish . ok . Opnd.V) (finish ovf))

||| A switch on distinct keys. A producer whose keys are computed decides
||| them (`choose`) and passes the proof.
export
switch : {auto 0 int : IsInt t} -> Opnd v t -> (cases : List (Int64, End d c m v l)) ->
         {auto 0 ok : So (Data.Distinct.distinct (map Builtin.fst cases)
                          && Body.keysFit t (map Builtin.fst cases))} ->
         End d c m v l -> End d c m v l
switch x cases {ok} dflt =
  MkBuild (\_ => PSwitch x (map Builtin.fst cases) {ok} (bodies cases) (finish dflt))
  where
    bodies : (cs : List (Int64, End d c m v l)) -> All (\_ => PBody d c m v l) (map Builtin.fst cs)
    bodies [] = []
    bodies ((_, b) :: cs) = finish b :: bodies cs

------------------------------------------------------------------------------
-- Into the term

data Lvl : IRCommon.Ty enc -> Type where
  MkLvl : {t : IRCommon.Ty enc} -> Nat -> Lvl t

data LLvl : List (IRCommon.Ty enc) -> Type where
  MkLLvl : {ps : List (IRCommon.Ty enc)} -> Nat -> LLvl ps

-- The variables bound in front of a context of d entries, as levels.
levels : (d : Nat) -> (ts : List (IRCommon.Ty enc)) -> All Lvl ts
levels d ts = go ts (length ts)
  where
    go : (us : List (IRCommon.Ty enc)) -> Nat -> All Lvl us
    go [] _ = []
    go (_ :: us) k = MkLvl (d + minus k 1) :: go us (minus k 1)

-- The label context `ls` and the context `ctx` come as random-access lists
-- of their own types (`RAList.fromList`), `labels` and `types`, each with
-- its depth, which the erased proofs keep in step with it. The position of
-- level n in a context of d entries is d - 1 - n, and the type there is
-- read and compared with the level's in steps of the order of the
-- logarithm of d (`Var.varAt`): walking the list to the position, a body
-- whose instructions read binders far below cost the square of its length.
cases : {0 ls : List (List (IRCommon.Ty enc))} -> Data.RAList Singleton ls -> (dl : Nat) ->
        (0 _ : dl = length ls) ->
        {0 ctx : List (IRCommon.Ty enc)} -> Data.RAList Singleton ctx -> (dc : Nat) ->
        (0 _ : dc = length ctx) ->
        All (\_ => PBody d c m Lvl LLvl) keys -> Maybe (All (\_ => Body d c m ls ctx) keys)

toBody : {0 ls : List (List (IRCommon.Ty enc))} -> Data.RAList Singleton ls -> (dl : Nat) ->
         (0 _ : dl = length ls) ->
         {0 ctx : List (IRCommon.Ty enc)} -> Data.RAList Singleton ctx -> (dc : Nat) ->
         (0 _ : dc = length ctx) ->
         PBody d c m Lvl LLvl -> Maybe (Body d c m ls ctx)
toBody labels dl pl types dc pc body = case body of
  PBind {ts} i k =>
    [| Body.Bind (Instr.traverseInstr (opnd types dc pc) i)
            (toBody labels dl pl (extend ts types) (length ts + dc) (plusLength pc)
              (k (levels dc ts))) |]
  PJoin ps b r => do
    let lbl = MkLLvl {ps} dl
        labels' = Val ps :: labels
    b' <- toBody labels' (S dl) (cong S pl) (extend ps types) (length ps + dc) (plusLength pc)
      (b lbl (levels dc ps))
    r' <- toBody labels' (S dl) (cong S pl) types dc pc (r lbl)
    pure (Body.Join ps b' r')
  PJump lbl xs =>
    [| Body.Jump (label labels dl pl lbl) (Opnd.traverseAll (opnd types dc pc) xs) |]
  PBranch {int} r x y a b =>
    [| (\x', y', a', b' => Body.Branch {int} r x' y' a' b')
         (opnd types dc pc x) (opnd types dc pc y) (toBody labels dl pl types dc pc a)
           (toBody labels dl pl types dc pc b) |]
  PIfFixnums {fx} {n} vs y no =>
    [| (\vs', y', no' => Body.IfFixnums {fx} vs' y' no')
         (traverse (opnd types dc pc) vs)
         (toBody labels dl pl (extend (replicate (S n) (IRCommon.Ty.Fix {enc})) types)
           (length (the (List (IRCommon.Ty enc)) (replicate (S n) IRCommon.Ty.Fix)) + dc)
                 (plusLength {ts = replicate (S n) (IRCommon.Ty.Fix {enc})} pc)
                 (y (levels dc _)))
         (toBody labels dl pl types dc pc no) |]
  PArithOv {t} {int} o x y ok ovf =>
    [| (\x', y', ok', ovf' => Body.ArithOv {t} {int} o x' y' ok' ovf')
         (opnd types dc pc x) (opnd types dc pc y)
         (toBody labels dl pl (Val t :: types) (S dc) (cong S pc) (ok (MkLvl dc)))
           (toBody labels dl pl types dc pc ovf) |]
  PTagOv {fx} x ok ovf =>
    [| (\x', ok', ovf' => Body.TagOv {fx} x' ok' ovf')
         (opnd types dc pc x)
         (toBody labels dl pl (Val (IRCommon.Ty.Fix {enc}) :: types) (S dc) (cong S pc)
           (ok (MkLvl dc)))
           (toBody labels dl pl types dc pc ovf) |]
  PSwitch {int} {ok} x keys bs dflt => do
    x' <- opnd types dc pc x
    bs' <- cases labels dl pl types dc pc bs
    dflt' <- toBody labels dl pl types dc pc dflt
    pure (Body.Switch {int} x' keys {ok} bs' dflt')
  PCall f xs k =>
    [| Body.Call (pure f) (Opnd.traverseAll (opnd types dc pc) xs)
      (toBody labels dl pl (Val IRCommon.Ty.Val :: types) (S dc) (cong S pc) (k (MkLvl dc))) |]
  PTailCall f xs => Body.TailCall f <$> Opnd.traverseAll (opnd types dc pc) xs
  PApply f x k =>
    [| Body.Apply (opnd types dc pc f) (opnd types dc pc x)
      (toBody labels dl pl (Val IRCommon.Ty.Val :: types) (S dc) (cong S pc) (k (MkLvl dc))) |]
  PTailApply f x => [| Body.TailApply (opnd types dc pc f) (opnd types dc pc x) |]
  PReturn x => Body.Return <$> opnd types dc pc x
  PEnter f xs => [| Body.Enter (opnd types dc pc f) (traverse (opnd types dc pc) xs) |]
  PRet xs => Body.Ret <$> Opnd.traverseAll (opnd types dc pc) xs
  PCrash s => Just (Body.Crash s)
  PUnsupported s => Just (Body.Unsupported s)
  where
    label : {0 ls' : List (List (IRCommon.Ty enc))} -> Data.RAList Singleton ls' -> (dl : Nat) ->
            (0 _ : dl = length ls') -> LLvl ps -> Maybe (Var ls' ps)
    label labels dl _ (MkLLvl n) = if n < dl then Var.varAt (minus dl (S n)) ps labels else Nothing

    opnd : {0 ctx' : List (IRCommon.Ty enc)} -> Data.RAList Singleton ctx' -> (dc : Nat) ->
           (0 _ : dc = length ctx') -> Opnd Lvl t -> Maybe (Opnd (Var ctx') t)
    opnd types dc pc (Opnd.V x) = Opnd.V <$> var types dc pc x
      where
        var : {0 ctx'' : List (IRCommon.Ty enc')} -> Data.RAList Singleton ctx'' -> (dc : Nat) ->
              (0 _ : dc = length ctx'') -> Lvl t' -> Maybe (Var ctx'' t')
        var types dc _ (MkLvl n) = if n < dc then Var.varAt (minus dc (S n)) t' types else Nothing
    opnd types dc _ (Opnd.W i) = Just (Opnd.W i)
    opnd types dc _ (Opnd.Fx {fx} {ok} i) = Just (Opnd.Fx {fx} {ok} i)
    opnd types dc _ (Opnd.Vx {fx} {ok} i) = Just (Opnd.Vx {fx} {ok} i)
    opnd types dc _ Opnd.Erased = Just Opnd.Erased

    -- A context extended at the top by the types.
    extend : (ts : List a) -> Data.RAList Singleton xs -> Data.RAList Singleton (ts ++ xs)
    extend [] rest = rest
    extend (t :: ts) rest = Val t :: extend ts rest

    -- The depth of a context extended at the top.
    plusLength : {ts, ctx' : List a} -> dc' = length ctx' -> length ts + dc' = length (ts ++ ctx')
    plusLength Refl = sym (appendLength ts ctx')
      where
        appendLength : (xs, ys : List a) -> length (xs ++ ys) = length xs + length ys
        appendLength [] ys = Refl
        appendLength (x :: xs) ys = cong S (appendLength xs ys)

cases labels dl pl types dc pc [] = Just []
cases labels dl pl types dc pc (b :: bs) =
  [| toBody labels dl pl types dc pc b :: cases labels dl pl types dc pc bs |]

||| A closed body as a term over its parameters.
export
close : {ps : List (IRCommon.Ty enc)} -> Closed d c m ps -> Maybe (Body d c m [] ps)
close t = toBody [] 0 Refl (Data.RAList.fromList ps) (length ps) Refl (t (levels 0 ps))
