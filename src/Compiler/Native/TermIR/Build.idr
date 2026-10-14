||| How producers build the term IR (`Compiler.Native.TermIR.Program`).
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
module Compiler.Native.TermIR.Build

import Compiler.Native.TermIR.Body as TermIR
import Compiler.Native.TermIR.Decls as TermIR
import Compiler.Native.TermIR.Instr as TermIR
import Compiler.Native.TermIR.IsInt as TermIR
import Compiler.Native.TermIR.Opnd as TermIR
import Compiler.Native.TermIR.OvOp as TermIR
import Compiler.Native.TermIR.Sig as TermIR
import Compiler.Native.TermIR.Var as TermIR

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Operators
import Compiler.Native.IRCommon.Ty
import Core.Name
import Data.Distinct
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.Vect
import Decidable.Equality

%default total

------------------------------------------------------------------------------
-- Bodies with binders

||| A body whose binders are functions, mirroring `Body`.
export
data PBody : Decls enc -> Conv enc -> Bool -> (v : Ty enc -> Type) -> (l : List (Ty enc) -> Type) -> Type where
  PBind : {ts : List (Ty enc)} -> Instr d m v ts -> (All v ts -> PBody d c m v l) -> PBody d c m v l
  PJoin : (ps : List (Ty enc)) -> (l ps -> All v ps -> PBody d c m v l) -> (l ps -> PBody d c m v l) ->
          PBody d c m v l
  PJump : l ps -> All (Opnd v) ps -> PBody d c m v l
  PBranch : {auto 0 int : IsInt t} -> Rel -> Opnd v t -> Opnd v t -> (yes, no : PBody d c m v l) -> PBody d c m v l
  PIfFixnums : {auto 0 fx : HasFixnums enc.val} ->
               {n : Nat} -> Vect (S n) (Opnd v Val) ->
               (All v (replicate (S n) (Fix {enc})) -> PBody d c m v l) -> PBody d c m v l -> PBody d c m v l
  PArithOv : {t : Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Opnd v t -> Opnd v t ->
             (v t -> PBody d c m v l) -> PBody d c m v l -> PBody d c m v l
  PTagOv : {auto 0 fx : HasFixnums enc.val} ->
           Opnd v W64 -> (v (Fix {enc}) -> PBody d c m v l) -> PBody d c m v l -> PBody d c m v l
  PSwitch : {auto 0 int : IsInt t} -> Opnd v t -> (keys : List Int64) ->
            {auto 0 ok : So (distinct keys && keysFit t keys)} ->
            All (\_ => PBody d c m v l) keys -> PBody d c m v l -> PBody d c m v l
  PCall : Var d.sigs (MkSig n CPS ps cv) -> All (Opnd v) ps -> (v Val -> PBody d CPS m v l) ->
          PBody d CPS m v l
  PTailCall : Var d.sigs (MkSig n CPS ps cv) -> All (Opnd v) ps -> PBody d CPS m v l
  PApply : (fn, arg : Opnd v Val) -> (v Val -> PBody d CPS m v l) -> PBody d CPS m v l
  PTailApply : (fn, arg : Opnd v Val) -> PBody d CPS m v l
  PReturn : Opnd v Val -> PBody d CPS m v l
  PEnter : Opnd v W64 -> List (Opnd v Val) -> PBody d c m v l
  PRet : All (Opnd v) rs -> PBody d (Direct rs col) m v l
  PCrash : String -> PBody d c m v l
  PUnsupported : String -> PBody d c m v l

||| A closed body over parameters of the types: parametric in its
||| variables and labels.
public export
0 Closed : Decls enc -> Conv enc -> Bool -> List (Ty enc) -> Type
Closed d c m ps = {0 v : Ty enc -> Type} -> {0 l : List (Ty enc) -> Type} -> All v ps -> PBody d c m v l

------------------------------------------------------------------------------
-- `Build`

||| Code that, given the rest of the body, makes the body.
public export
record Build (d : Decls enc) (c : Conv enc) (m : Bool) (v : Ty enc -> Type) (l : List (Ty enc) -> Type) (a : Type) where
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
0 End : Decls enc -> Conv enc -> Bool -> (Ty enc -> Type) -> (List (Ty enc) -> Type) -> Type
End d c m v l = Build d c m v l Void

||| The body that code ending in a terminator makes.
export
finish : End d c m v l -> PBody d c m v l
finish b = b.run absurd

vars : All v qs -> All (Opnd v) qs
vars [] = []
vars (x :: xs) = V x :: vars xs

||| A body from `Build` code over the parameters.
export
build : ({0 v : Ty enc -> Type} -> {0 l : List (Ty enc) -> Type} -> All (Opnd v) ps -> End d c m v l) ->
        Closed d c m ps
build f xs = finish (f (vars xs))

||| An instruction, binding its results.
export
emit : {ts : List (Ty enc)} -> Instr d m v ts -> Build d c m v l (All v ts)
emit i = MkBuild (PBind i)

||| An instruction of one result.
export
emit1 : {t : Ty enc} -> Instr d m v [t] -> Build d c m v l (Opnd v t)
emit1 i = MkBuild (\k => PBind i (\[x] => k (V x)))

||| An instruction of no result.
export
emit0 : Instr d m v [] -> Build d c m v l ()
emit0 i = MkBuild (\k => PBind i (\[] => k ()))

||| A Direct call, binding its results.
export
directCall : {rs : List (Ty enc)} -> Var d.sigs (MkSig n (Direct rs col) ps cv) -> All (Opnd v) ps ->
             Build d c m v l (All (Opnd v) rs)
directCall f xs = vars <$> emit (DirectCall f xs)

||| A CPS call: the rest of the code is its continuation.
export
call : Var d.sigs (MkSig n CPS ps cv) -> All (Opnd v) ps -> Build d CPS m v l (Opnd v Val)
call f xs = MkBuild (\k => PCall f xs (k . V))

||| A closure applied to one argument: the rest of the code is its
||| continuation.
export
apply : (fn, arg : Opnd v Val) -> Build d CPS m v l (Opnd v Val)
apply f x = MkBuild (\k => PApply f x (k . V))

export
tailCall : Var d.sigs (MkSig n CPS ps cv) -> All (Opnd v) ps -> End d CPS m v l
tailCall f xs = MkBuild (\_ => PTailCall f xs)

export
tailApply : (fn, arg : Opnd v Val) -> End d CPS m v l
tailApply f x = MkBuild (\_ => PTailApply f x)

export
return : Opnd v Val -> End d CPS m v l
return x = MkBuild (\_ => PReturn x)

export
ret : All (Opnd v) rs -> End d (Direct rs col) m v l
ret xs = MkBuild (\_ => PRet xs)

export
enter : Opnd v W64 -> List (Opnd v Val) -> End d c m v l
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
0 Jumper : Decls enc -> Conv enc -> Bool -> (Ty enc -> Type) -> (List (Ty enc) -> Type) -> List (Ty enc) -> Type
Jumper d c m v l ps = All (Opnd v) ps -> End d c m v l

jumpTo : l ps -> Jumper d c m v l ps
jumpTo lbl xs = MkBuild (\_ => PJump lbl xs)

||| A block with parameters, which the rest of the code may jump to.
export
block : (ps : List (Ty enc)) -> (All (Opnd v) ps -> End d c m v l) -> Build d c m v l (Jumper d c m v l ps)
block ps body = MkBuild (\k => PJoin ps (\_, xs => finish (body (vars xs))) (\lbl => k (jumpTo lbl)))

||| A join: the code given ends by jumping to the exit with values, and the
||| rest of the code runs on them, lowered once.
export
joinPoint : (ps : List (Ty enc)) -> (Jumper d c m v l ps -> End d c m v l) -> Build d c m v l (All (Opnd v) ps)
joinPoint ps f = MkBuild (\k => PJoin ps (\_, xs => k (vars xs)) (\lbl => finish (f (jumpTo lbl))))

||| A loop: the body runs on the initial values and may jump back with new
||| ones. It leaves only through an enclosing join or a terminator.
export
loop : (ps : List (Ty enc)) -> All (Opnd v) ps ->
       (Jumper d c m v l ps -> All (Opnd v) ps -> End d c m v l) -> End d c m v l
loop ps init body =
  MkBuild (\_ => PJoin ps (\lbl, xs => finish (body (jumpTo lbl) (vars xs))) (\lbl => PJump lbl init))

||| Compare two integers and branch.
export
branch : {auto 0 int : IsInt t} -> Rel -> Opnd v t -> Opnd v t -> (yes, no : End d c m v l) -> End d c m v l
branch r x y yes no = MkBuild (\_ => PBranch r x y (finish yes) (finish no))

||| Leave by the code given when the relation holds; else go on.
export
leaveIf : {auto 0 int : IsInt t} -> Rel -> Opnd v t -> Opnd v t -> End d c m v l -> Build d c m v l ()
leaveIf r x y out = MkBuild (\k => PBranch r x y (finish out) (k ()))

||| Whether every value is a fixnum; the yes branch has them as `Fix`es.
||| An immediate is a fixnum (the erased value is fixnum 0), so only the
||| variables are tested, and with none the yes branch is taken outright.
export
ifFixnums : {auto 0 fx : HasFixnums enc.val} -> {n : Nat} -> Vect (S n) (Opnd v Val) ->
            (All (Opnd v) (replicate (S n) (Fix {enc})) -> End d c m v l) -> End d c m v l -> End d c m v l
ifFixnums vs yes no = case variables vs of
    [] => yes (fixes (fill vs []))
    (t :: ts) => MkBuild (\_ => PIfFixnums (V t :: map V (fromList ts))
                                   (\fs => finish (yes (fixes (fill vs (narrowed {k = S (length ts)} fs)))))
                                   (finish no))
  where
    -- The values to test: the variables.
    variables : Vect j (Opnd v Val) -> List (v Val)
    variables [] = []
    variables (V x :: xs) = x :: variables xs
    variables (_ :: xs) = variables xs

    -- The tested values, narrowed, in order.
    narrowed : {k : Nat} -> All v (replicate k (Fix {enc})) -> List (v (Fix {enc}))
    narrowed {k = Z} [] = []
    narrowed {k = S k} (f :: fs) = f :: narrowed fs

    -- Each value as a `Fix`: an immediate as itself, a variable as the next
    -- narrowed one.
    fill : Vect j (Opnd v Val) -> List (v (Fix {enc})) -> Vect j (Opnd v (Fix {enc}))
    fill [] _ = []
    fill (Vx {ok} i :: xs) fs = Fx {ok} i :: fill xs fs
    fill (Erased :: xs) fs = Fx 0 :: fill xs fs
    fill (V _ :: xs) (f :: fs) = V f :: fill xs fs
    fill (V _ :: xs) [] = Fx 0 :: fill xs []   -- not reached: one narrowed value per variable

    fixes : Vect j (Opnd v (Fix {enc})) -> All (Opnd v) (replicate j (Fix {enc}))
    fixes [] = []
    fixes (x :: xs) = x :: fixes xs

||| Arithmetic with its overflow branch.
export
arithOv : {t : Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Opnd v t -> Opnd v t ->
          (Opnd v t -> End d c m v l) -> End d c m v l -> End d c m v l
arithOv o x y ok ovf = MkBuild (\_ => PArithOv o x y (finish . ok . V) (finish ovf))

||| The fixnum of a word, with the branch for a word out of range.
export
tagOv : {auto 0 fx : HasFixnums enc.val} -> Opnd v W64 ->
        (Opnd v (Fix {enc}) -> End d c m v l) -> End d c m v l -> End d c m v l
tagOv x ok ovf = MkBuild (\_ => PTagOv x (finish . ok . V) (finish ovf))

||| A switch on distinct keys. A producer whose keys are computed decides
||| them (`choose`) and passes the proof.
export
switch : {auto 0 int : IsInt t} -> Opnd v t -> (cases : List (Int64, End d c m v l)) ->
         {auto 0 ok : So (distinct (map Builtin.fst cases) && keysFit t (map Builtin.fst cases))} ->
         End d c m v l -> End d c m v l
switch x cases {ok} dflt = MkBuild (\_ => PSwitch x (map Builtin.fst cases) {ok} (bodies cases) (finish dflt))
  where
    bodies : (cs : List (Int64, End d c m v l)) -> All (\_ => PBody d c m v l) (map Builtin.fst cs)
    bodies [] = []
    bodies ((_, b) :: cs) = finish b :: bodies cs

------------------------------------------------------------------------------
-- Into the term

data Lvl : Ty enc -> Type where
  MkLvl : {t : Ty enc} -> Nat -> Lvl t

data LLvl : List (Ty enc) -> Type where
  MkLLvl : {ps : List (Ty enc)} -> Nat -> LLvl ps

-- The variables bound in front of a context of d entries, as levels.
levels : (d : Nat) -> (ts : List (Ty enc)) -> All Lvl ts
levels d ts = go ts (length ts)
  where
    go : (us : List (Ty enc)) -> Nat -> All Lvl us
    go [] _ = []
    go (_ :: us) k = MkLvl (d + minus k 1) :: go us (minus k 1)

cases : (ls : List (List (Ty enc))) -> (dl : Nat) -> (0 _ : dl = length ls) ->
        (ctx : List (Ty enc)) -> (dc : Nat) -> (0 _ : dc = length ctx) ->
        All (\_ => PBody d c m Lvl LLvl) keys -> Maybe (All (\_ => Body d c m ls ctx) keys)

toBody : (ls : List (List (Ty enc))) -> (dl : Nat) -> (0 _ : dl = length ls) ->
         (ctx : List (Ty enc)) -> (dc : Nat) -> (0 _ : dc = length ctx) ->
         PBody d c m Lvl LLvl -> Maybe (Body d c m ls ctx)
toBody ls dl pl ctx dc pc body = case body of
  PBind {ts} i k =>
    [| Bind (traverseInstr (opnd ctx dc pc) i)
            (toBody ls dl pl (ts ++ ctx) (length ts + dc) (plusLength pc) (k (levels dc ts))) |]
  PJoin ps b r => do
    let lbl = MkLLvl {ps} dl
    b' <- toBody (ps :: ls) (S dl) (cong S pl) (ps ++ ctx) (length ps + dc) (plusLength pc) (b lbl (levels dc ps))
    r' <- toBody (ps :: ls) (S dl) (cong S pl) ctx dc pc (r lbl)
    pure (Join ps b' r')
  PJump lbl xs => [| Jump (label ls dl pl lbl) (traverseAll (opnd ctx dc pc) xs) |]
  PBranch {int} r x y a b =>
    [| (\x', y', a', b' => Branch {int} r x' y' a' b')
         (opnd ctx dc pc x) (opnd ctx dc pc y) (toBody ls dl pl ctx dc pc a) (toBody ls dl pl ctx dc pc b) |]
  PIfFixnums {fx} {n} vs y no =>
    [| (\vs', y', no' => IfFixnums {fx} vs' y' no')
         (traverse (opnd ctx dc pc) vs)
         (toBody ls dl pl (replicate (S n) (Fix {enc}) ++ ctx) (length (the (List (Ty enc)) (replicate (S n) Fix)) + dc)
                 (plusLength {ts = replicate (S n) (Fix {enc})} pc)
                 (y (levels dc _)))
         (toBody ls dl pl ctx dc pc no) |]
  PArithOv {t} {int} o x y ok ovf =>
    [| (\x', y', ok', ovf' => ArithOv {t} {int} o x' y' ok' ovf')
         (opnd ctx dc pc x) (opnd ctx dc pc y)
         (toBody ls dl pl (t :: ctx) (S dc) (cong S pc) (ok (MkLvl dc))) (toBody ls dl pl ctx dc pc ovf) |]
  PTagOv {fx} x ok ovf =>
    [| (\x', ok', ovf' => TagOv {fx} x' ok' ovf')
         (opnd ctx dc pc x)
         (toBody ls dl pl (Fix {enc} :: ctx) (S dc) (cong S pc) (ok (MkLvl dc))) (toBody ls dl pl ctx dc pc ovf) |]
  PSwitch {int} {ok} x keys bs dflt => do
    x' <- opnd ctx dc pc x
    bs' <- cases ls dl pl ctx dc pc bs
    dflt' <- toBody ls dl pl ctx dc pc dflt
    pure (Switch {int} x' keys {ok} bs' dflt')
  PCall f xs k =>
    [| Call (pure f) (traverseAll (opnd ctx dc pc) xs) (toBody ls dl pl (Val :: ctx) (S dc) (cong S pc) (k (MkLvl dc))) |]
  PTailCall f xs => TailCall f <$> traverseAll (opnd ctx dc pc) xs
  PApply f x k =>
    [| Apply (opnd ctx dc pc f) (opnd ctx dc pc x) (toBody ls dl pl (Val :: ctx) (S dc) (cong S pc) (k (MkLvl dc))) |]
  PTailApply f x => [| TailApply (opnd ctx dc pc f) (opnd ctx dc pc x) |]
  PReturn x => Return <$> opnd ctx dc pc x
  PEnter f xs => [| Enter (opnd ctx dc pc f) (traverse (opnd ctx dc pc) xs) |]
  PRet xs => Ret <$> traverseAll (opnd ctx dc pc) xs
  PCrash s => Just (Crash s)
  PUnsupported s => Just (Unsupported s)
  where
    label : (ls : List (List (Ty enc'))) -> (dl : Nat) -> (0 _ : dl = length ls) -> LLvl ps -> Maybe (Var ls ps)
    label ls dl _ (MkLLvl n) = if n < dl then varAt (minus dl (S n)) ps ls else Nothing

    opnd : (ctx : List (Ty enc'')) -> (dc : Nat) -> (0 _ : dc = length ctx) -> Opnd Lvl t -> Maybe (Op ctx t)
    opnd ctx dc pc (V x) = V <$> var ctx dc pc x
      where
        -- The position of level n in a context of d entries is d - 1 - n. The
        -- depth comes with the context, so that a variable costs its distance from
        -- the top of the context and not the context's length, which made a long
        -- body cost the square of its length; the erased proof keeps the two in
        -- step.
        var : (ctx : List (Ty enc')) -> (dc : Nat) -> (0 _ : dc = length ctx) -> Lvl t' -> Maybe (Var ctx t')
        var ctx dc _ (MkLvl n) = if n < dc then varAt (minus dc (S n)) t' ctx else Nothing
    opnd ctx dc _ (W i) = Just (W i)
    opnd ctx dc _ (Fx {fx} {ok} i) = Just (Fx {fx} {ok} i)
    opnd ctx dc _ (Vx {fx} {ok} i) = Just (Vx {fx} {ok} i)
    opnd ctx dc _ Erased = Just Erased

    -- The depth of a context extended at the top.
    plusLength : {ts, ctx' : List a} -> dc' = length ctx' -> length ts + dc' = length (ts ++ ctx')
    plusLength Refl = sym (appendLength ts ctx')
      where
        appendLength : (xs, ys : List a') -> length (xs ++ ys) = length xs + length ys
        appendLength [] ys = Refl
        appendLength (x :: xs) ys = cong S (appendLength xs ys)

cases ls dl pl ctx dc pc [] = Just []
cases ls dl pl ctx dc pc (b :: bs) = [| toBody ls dl pl ctx dc pc b :: cases ls dl pl ctx dc pc bs |]

||| A closed body as a term over its parameters.
export
close : {ps : List (Ty enc)} -> Closed d c m ps -> Maybe (Body d c m [] ps)
close t = toBody [] 0 Refl ps (length ps) Refl (t (levels 0 ps))
