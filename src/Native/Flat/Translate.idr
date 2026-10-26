||| The flat translation: from a definition's typed case tree to its flat form
||| (`Flat.Exp`), the form of the definition in the flat regime, in which
||| every value is held in registers and none needs the heap.
|||
||| The translation reads the compile-time case tree of a definition, whose
||| terms are full: every subterm's type can be found. It walks the tree with
||| the run-time arguments as *flat variables*, each a register-held value of a
||| type with a layout, and every other value as a *static* term, a closed term
||| that the translation reduces instead of computing at run time: a type, a
||| dictionary, a function, an `IO` action. Flat variables are `Bound`
||| references in the closed terms, so that a static term can mention them.
|||
||| A static term is reduced where its value is needed: a lambda that is
||| applied, a `let` of a static value, a case on a known constructor or
||| constant, a primitive operation on constants, and a call of a definition
||| that is *unfolded*: one marked inline (methods and implementations are),
||| a case or with block, `io_bind`, `prim__io_bind` and `idris_crash`.
|||
||| A definition is unfolded everywhere except in terms written inside its
||| own body, where it is called instead, so unfolding ends: every term
||| unfolded is written inside one more definition. A static term passed into
||| a body keeps the definitions it was written inside, as a *closure*: a
||| `Bound` name that stands for it. So a dictionary that its own default
||| methods refer to unfolds where a program uses it, and the continuation
||| of a `do` block unfolds `io_bind` although an `io_bind` is applying it.
|||
||| A call of any other function is a call of a flat form of it, made on
||| demand and memoised: a form being made counts as made, so recursion ends.
||| A function whose signature is *ground*, every run-time argument and its
||| result laid out with no erased argument deciding a layout, has one form,
||| its own. A call of any other function is at *static arguments*: erased
||| ones, dictionaries, functions, lazy values, and closed values without a
||| layout. It is a call of a *copy* of the function made for them: the
||| function's case tree with the static arguments substituted, which keeps
||| it typed, translated as any form is. A copy's parameters are the call's
||| other, flat arguments, and then the flat variables the static arguments
||| capture, such as those a lambda refers to, renamed in the copy; so one
||| copy, keyed by the function and its static terms, serves every call
||| whose static arguments are the same. Copies of one function nest only
||| when it calls itself at other static arguments, and a chain that nests
||| them too deep is reported, since such arguments can grow without end.
|||
||| A function whose result is a newtype over a function (`IO a`) takes that
||| function's arguments as its own, as `checkFlatSignature` walks it, so a
||| term of such a type is translated *applied* to the arguments its context
||| has not given it yet: the pending arguments. A static value of such a
||| type that does not reduce to its constructor, such as the call `putc c`
||| of a function, is taken apart by giving its function a name that stands
||| for the value applied to the pending arguments.
|||
||| A constant that a directive marks static, whose value the code
||| generator computes as it compiles the program, is neither unfolded nor
||| called: a read of it is its value (`FStatic`), where flat code holds
||| that as ordinary code holds it, in one uniform register, or where it is
||| a machine scalar. One of any other layout is called, its form computing
||| it.
|||
||| Whatever the translation cannot place in the regime, it reports as
||| `NotFlatBody` (`Flat.Problem`), with the chain of calls from the flat
||| function it started from to it.
|||
||| The flat functions and the static constants are the ones a code
||| generator's directives name (`markedNames`), and everything the flat
||| functions call is translated in turn. The translation runs on the whole
||| context, the imported modules' case trees included, and keeps the forms
||| it makes for the one compilation or check that asked for them.
module Native.Flat.Translate

import Native.Flat.Definition
import Native.Flat.Exp
import Native.Flat.Judgement
import Native.Flat.Problem

import Algebra
import Algebra.Preorder
import Algebra.Semiring
import Algebra.ZeroOneOmega
import Compiler.Opts.Constructor
import Core.Case.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Env
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Name.Scoped
import Core.Normalise.Eval
import Core.Normalise.Quote
import Core.Primitives
import Core.TT
import Core.TT.Binder
import Core.TT.Primitive
import Core.TT.Subst
import Core.TT.Term
import Core.TT.Term.Subst
import Core.TT.Var
import Core.Value
import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.String
import Data.Vect
import Data.Zippable
import Libraries.Data.List.SizeOf
import Libraries.Data.List.Thin
import Libraries.Data.NameMap
import Libraries.Data.WithDefault
import Native.Data.Builder as Data
import Native.Data.WriteBuilder
import Native.Rep
import System.File
import System.File.ReadWrite

%default covering

||| What a name that stands for a static value stands for.
data Static : Type where
  ||| A term, with the definitions it was written inside.
  Closure : (term : ClosedTerm) -> (origin : List Name) -> Static
  ||| The function inside `value`, a value of a newtype over a function
  ||| (`IO`) that does not reduce to the newtype's constructor, with the
  ||| definitions `value` was written inside.
  Unwrapped : (value : ClosedTerm) -> (origin : List Name) -> Static

||| A copy of a function at static arguments: the function, the key that
||| tells its static arguments apart (one entry per argument, `Nothing` for a
||| dynamic one), and the name of the copy's form.
record Copy where
  constructor MkCopy
  function : Name
  key : List (Maybe ClosedTerm)
  form : Name

||| The translation's state: the primitives, the constants the program
||| marks static, a counter for the names it makes, the forms being made,
||| which count as made, the static values that names stand for, the forms
||| made, the copies made, and the problem the translation stopped at,
||| which `fail` records.
record FlatState where
  constructor MkFlatState
  primitives : List Name
  staticConstants : List Name
  nextName : Int
  making : List Name
  statics : NameMap Static
  forms : NameMap Exp.FlatDef
  copies : List Copy
  failure : Maybe Problem.FlatError

||| The label of the reference that holds the translation's state, a
||| `Ref FlatSt FlatState`, by which `get`, `put` and `update` find it among
||| the references in scope. It has no values: it is only ever a type.
data FlatSt : Type where

||| Where the translation is.
record Tr where
  constructor MkTr
  ||| the flat function whose form is being made
  root : Name
  ||| the callees from the root to the definition being translated, the
  ||| latest last
  chain : SnocList Name
  ||| the location in the root's own code that the translation left it from
  site : FC
  ||| the definitions the term being translated was written inside
  unfolding : List Name
  ||| the flat variables in scope, with their types
  vars : NameMap (Exp.FlatVar, ClosedTerm)

||| What a term is applied to beyond its own arguments.
data Pending : Type where
  ||| An argument.
  PArg : (arg : ClosedTerm) -> Pending
  ||| The unwrapping of a value of a newtype over a function, whose
  ||| function is applied to what follows.
  PUnwrap : Pending

-- Case and with blocks, which are part of the definition they are in.
blockName : Name -> Bool
blockName (CaseBlock {}) = True
blockName (WithBlock {}) = True
blockName (NS _ n) = blockName n
blockName (DN _ n) = blockName n
blockName _ = False

-- Whether the term being translated was written in the root's own code.
inRoot : Tr -> Bool
inRoot tr = isLin tr.chain && all (\n => n == tr.root || blockName n) tr.unfolding

-- Stop the translation at the problem, which is recorded in the state for
-- `flatForms` to report. It is at the term's location if the root's own code
-- has it, or else where the translation left the root's code.
fail : {auto s : Ref FlatSt FlatState} -> Tr -> FC -> Problem.FlatProblem -> Core a
fail tr fc p
    = do update FlatSt
           { failure := Just (Problem.NotFlatBody (if inRoot tr then nonEmpty fc else tr.site)
                                                       tr.root (tr.chain <>> []) p) }
         throw (InternalError "the flat translation stopped")
  where
    nonEmpty : FC -> FC
    nonEmpty EmptyFC = tr.site
    nonEmpty fc = fc

inside : List Name -> Tr -> Tr
inside ns tr = { unfolding := ns } tr

addVar : Exp.FlatVar -> ClosedTerm -> Tr -> Tr
addVar fv ty tr = { vars $= insert fv.name (fv, ty) } tr

fresh : {auto s : Ref FlatSt FlatState} -> Name -> Core Name
fresh x
    = do st <- get FlatSt
         put FlatSt ({ nextName $= (+ 1) } st)
         pure (MN (nameRoot x) st.nextName)

-- A term that names a value without computing it.
isAtom : Tr -> ClosedTerm -> Bool
isAtom tr (Ref _ Bound x) = isJust (lookup x tr.vars)
isAtom tr (Ref _ (DataCon _ Z) _) = True
isAtom tr (PrimVal {}) = True
isAtom tr (Erased {}) = True
isAtom tr _ = False

-- A term about to leave the definitions it was written inside, as a closure.
static : {auto s : Ref FlatSt FlatState} -> Tr -> ClosedTerm -> Core ClosedTerm
static tr t@(Ref _ Bound _) = pure t
static tr t
    = if isAtom tr t then pure t else
        do x <- fresh (UN (Basic "static"))
           update FlatSt { statics $= insert x (Closure t tr.unfolding) }
           pure (Ref (getLoc t) Bound x)

-- A term with the names that stand for static values replaced by the
-- terms, so that a type made of them can be judged.
resolve : NameMap Static -> Term vars -> Term vars
resolve sts (Ref fc Bound x)
    = case lookup x sts of
           Just (Closure t _) => embed (resolve sts t)
           _ => Ref fc Bound x
resolve sts (Bind fc x b sc) = Bind fc x (map (resolve sts) b) (resolve sts sc)
resolve sts (App fc f a) = App fc (resolve sts f) (resolve sts a)
resolve sts (As fc u a p) = As fc u (resolve sts a) (resolve sts p)
resolve sts (TDelayed fc r t) = TDelayed fc r (resolve sts t)
resolve sts (TDelay fc r t v) = TDelay fc r (resolve sts t) (resolve sts v)
resolve sts (TForce fc r t) = TForce fc r (resolve sts t)
resolve sts (Meta fc n i args) = Meta fc n i (map (resolve sts) args)
resolve sts tm = tm

resolved : {auto s : Ref FlatSt FlatState} -> ClosedTerm -> Core ClosedTerm
resolved tm = pure (resolve (statics !(get FlatSt)) tm)

mkSubst : (vars : Scope) -> List ClosedTerm -> Maybe (SubstEnv vars Scope.empty)
mkSubst [] [] = Just []
mkSubst (_ :: vs) (t :: ts) = (t ::) <$> mkSubst vs ts
mkSubst _ _ = Nothing

extendSubst : (args : List Name) -> List ClosedTerm ->
              SubstEnv vars Scope.empty -> Maybe (SubstEnv (args ++ vars) Scope.empty)
extendSubst [] [] env = Just env
extendSubst (_ :: ns) (t :: ts) env = (t ::) <$> extendSubst ns ts env
extendSubst _ _ _ = Nothing

instantiate : {vars : _} -> SubstEnv vars Scope.empty -> Term vars -> ClosedTerm
instantiate env tm = substs (mkSizeOf vars) env (rewrite appendNilRightNeutral vars in tm)

quoteClosed : {auto c : Ref Ctxt Defs} -> ClosedNF -> Core ClosedTerm
quoteClosed ty
    = do defs <- get Ctxt
         quote defs Env.empty ty

||| A type's skeleton.
skeleton : {auto c : Ref Ctxt Defs} -> ClosedNF -> Core Exp.Skeleton
skeleton (NPrimVal _ (PrT t)) = pure (Exp.SPrim t)
skeleton (NTCon _ n _ args) = Exp.SCon !(toFullNames n) <$> traverse argSkeleton args
  where
    argSkeleton : (FC, ClosedClosure) -> Core Exp.Skeleton
    argSkeleton (_, a) = skeleton !(evalClosure !(get Ctxt) a)
skeleton (NDCon _ n _ _ args) = Exp.SCon !(toFullNames n) <$> traverse argSkeleton args
  where
    argSkeleton : (FC, ClosedClosure) -> Core Exp.Skeleton
    argSkeleton (_, a) = skeleton !(evalClosure !(get Ctxt) a)
skeleton _ = pure Exp.SOther

||| A type's skeleton and layout, or why it is not flat.
export
laidOut : {auto c : Ref Ctxt Defs} -> ClosedNF ->
          Core (Either Problem.NotFlatReason (Exp.Skeleton, Exp.Layout))
laidOut ty
    = case !(layout [] ty) of
           Judgement.LaidOut l => pure (Right (!(skeleton ty), l))
           Judgement.Rejected why => pure (Left why)
           Judgement.Deferred => pure (Left Problem.StuckType)

||| A binder of a function's type, at the argument given for it.
record Applied where
  constructor MkApplied
  name : Name
  rig : RigCount
  autoImplicit : Bool
  ||| its position among the explicit arguments, from 1, and its name
  position : Maybe (Nat, Name)
  type : ClosedNF

isExplicit : PiInfo t -> Bool
isExplicit Explicit = True
isExplicit _ = False

isAutoImplicit : PiInfo t -> Bool
isAutoImplicit AutoImplicit = True
isAutoImplicit _ = False

-- The binders of a function type `ty` applied to `args`, and the type of the
-- application.
applyType : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
            ClosedTerm -> List ClosedTerm -> Core (Maybe (List Applied, ClosedNF))
applyType ty args
    = do defs <- get Ctxt
         go 0 [] !(nf defs Env.empty ty) !(traverse resolved args)
  where
    go : Nat -> List Applied -> ClosedNF -> List ClosedTerm ->
         Core (Maybe (List Applied, ClosedNF))
    go i acc (NBind fc x (Pi _ rig pinfo aty) sc) (a :: as)
        = do defs <- get Ctxt
             let i' = if isExplicit pinfo then S i else i
             b <- pure (MkApplied x rig (isAutoImplicit pinfo) (Just (i', x))
                                  !(evalClosure defs aty))
             go i' (b :: acc) !(sc defs (toClosure defaultOpts Env.empty a)) as
    go i acc res [] = pure (Just (reverse acc, res))
    go i acc _ _ = pure Nothing

||| A part of a function's signature as the flat regime walks it.
data SigPart : Type where
  ||| A binder, with the variable that stands for its argument.
  SigArg : (binder : Applied) -> (var : Name) -> SigPart
  ||| A newtype over a function, unwrapped at the result, whose function's
  ||| binders follow.
  SigUnwrap : SigPart

record Signature where
  constructor MkSignature
  parts : List SigPart
  result : ClosedNF

-- The arguments of a call as static values, those of erased binders as they
-- are, so that types keep them.
staticArgs : {auto s : Ref FlatSt FlatState} ->
             Tr -> List (Applied, ClosedTerm) -> Core (List ClosedTerm)
staticArgs tr = traverse arg
  where
    arg : (Applied, ClosedTerm) -> Core ClosedTerm
    arg (b, a) = if isErased b.rig then pure a else static tr a

||| Whether a call of the definition is unfolded where the translation is:
||| one marked inline, a case or with block, or one the compiler's inliner
||| unfolds anyway, but in terms written inside its own body, and never a
||| constant the program marks static (`staticConstants`), which flat code
||| reads as the value the code generator computes.
unfoldable : (staticConstants : List Name) -> Tr -> Name -> GlobalDef -> Bool
unfoldable staticConstants tr fn gdef
    = let fl = gdef.flags in
          ((elem Inline fl && not (elem NoInline fl))
             || blockName fn || elem fn unfoldedAnyway)
          && not (elem fn tr.unfolding) && not (elem fn staticConstants)
  where
    -- The definitions the compiler's inliner unfolds although they are not
    -- marked inline.
    unfoldedAnyway : List Name
    unfoldedAnyway
        = [ NS primIONS (UN (Basic "io_bind"))
          , NS primIONS (UN (Basic "prim__io_bind"))
          , NS builtinNS (UN (Basic "idris_crash"))
          ]

||| A term with each `let` whose variable its scope does not use dropped.
||| A case tree keeps the case block's binding of the scrutinee to its
||| pattern around a term elaborated in an alternative, as the dictionary
||| of a `fromString` that Idris leaves unreduced, for a literal of ten
||| characters or more: the binding's value names the pattern's variables,
||| flat ones, which the term does not use, and without it the term is
||| closed.
deadLets : Term vs -> Term vs
deadLets (Bind fc x b@(Let {}) sc) = case shrink (deadLets sc) (Drop Refl) of
  Just sc' => sc'
  Nothing => Bind fc x b (deadLets sc)
deadLets (Bind fc x b sc) = Bind fc x b (deadLets sc)
deadLets (App fc f a) = App fc (deadLets f) (deadLets a)
deadLets t = t

-- The type of a static value that does not reduce: the type of the call it
-- is, or else the case tree's type for it.
stuckType : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
            {vars : _} ->
            SubstEnv vars Scope.empty -> ClosedTerm -> Term vars -> Core ClosedNF
stuckType env v scTy
    = do defs <- get Ctxt
         let (Ref _ _ n, args) = getFnArgs v
           | _ => fromTree
         Just gdef <- lookupCtxtExact n (gamma defs)
           | Nothing => fromTree
         Just (_, ty) <- applyType (type gdef) args
           | Nothing => fromTree
         pure ty
  where
    fromTree : Core ClosedNF
    fromTree = do defs <- get Ctxt
                  nf defs Env.empty !(resolved (instantiate env scTy))

-- The one constructor alternative of a case.
conCase : List (CaseAlt vars) ->
          Maybe (Name, (args : List Name ** CaseTree (Scope.addInner vars args)))
conCase [] = Nothing
conCase (ConCase cn _ args sc :: _) = Just (cn, (args ** sc))
conCase (_ :: as) = conCase as

-- The arguments of a constructor that a static value has, as static values
-- written where `tr` is.
conArgs : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
          Tr -> Name -> List ClosedTerm -> Core (List ClosedTerm)
conArgs tr cn cargs
    = do defs <- get Ctxt
         Just cdef <- lookupCtxtExact cn (gamma defs)
           | Nothing => pure cargs
         Just (bs, _) <- applyType (type cdef) cargs
           | Nothing => pure cargs
         staticArgs tr (zip bs cargs)

mutual

  -- The values of a constructor pattern's variables, at a scrutinee of type
  -- `tyNF`: a fresh flat variable for each run-time field, the type's
  -- argument for an erased binder the type's arguments give, and a fresh
  -- name for any other erased binder, which is never used at run time. For
  -- a static scrutinee of a newtype over a function, given with where it
  -- was written, the field is a name for it unwrapped instead.
  openCon : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
            Tr -> FC -> ClosedNF -> Name -> List Name ->
            (unwrapping : Maybe (ClosedTerm, List Name)) ->
            Core (List ClosedTerm, List Exp.FlatVar, Tr)
  openCon tr fc tyNF cn args unwrapping
      = do defs <- get Ctxt
           Just cdef <- lookupCtxtExact cn (gamma defs)
             | Nothing => undefinedName fc cn
           let tyArgs = case tyNF of
                             NTCon _ _ _ as => as
                             _ => []
           cty <- nf defs Env.empty (type cdef)
           ps <- resultPositions 0 cty
           bind ps tyArgs 0 args cty [] [] tr
    where
      placeholder : Nat -> Name
      placeholder i = MN "flat binder" (cast i)

      given : ClosedNF -> Maybe Nat
      given (NApp _ (NRef Bound (MN "flat binder" b)) []) = Just (cast b)
      given _ = Nothing

      -- (binder, argument position) for each binder the result gives as an
      -- argument of the type
      resultPositions : Nat -> ClosedNF -> Core (List (Nat, Nat))
      resultPositions i (NBind bfc _ (Pi {}) sc)
          = do defs <- get Ctxt
               resultPositions (S i)
                 !(sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound (placeholder i))))
      resultPositions i (NTCon _ _ _ res)
          = do defs <- get Ctxt
               vals <- traverse (evalClosure defs . snd) res
               pure (mapMaybe (\kv => map (\b => (b, fst kv)) (given (snd kv)))
                              (zip [0 .. length vals] vals))
      resultPositions i _ = pure []

      argAt : Nat -> List x -> Maybe x
      argAt _ [] = Nothing
      argAt Z (v :: _) = Just v
      argAt (S k) (_ :: vs) = argAt k vs

      bind : List (Nat, Nat) -> List (FC, ClosedClosure) -> Nat -> List Name -> ClosedNF ->
             List ClosedTerm -> List Exp.FlatVar -> Tr ->
             Core (List ClosedTerm, List Exp.FlatVar, Tr)
      bind ps tyArgs i (a :: as) (NBind bfc _ (Pi _ rig _ aty) sc) vals fvs tr
          = do defs <- get Ctxt
               atyNF <- evalClosure defs aty
               if isErased rig
                  then do val <- case lookup i ps >>= \k => argAt k tyArgs of
                                      Just (_, cl) => quoteClosed !(evalClosure defs cl)
                                      Nothing => pure (Ref bfc Bound !(fresh a))
                          sc' <- sc defs (toClosure defaultOpts Env.empty val)
                          bind ps tyArgs (S i) as sc' (val :: vals) fvs tr
                  else do v <- fresh a
                          let Nothing = unwrapping
                            | Just (u, origin) =>
                                do update FlatSt { statics $= insert v (Unwrapped u origin) }
                                   sc' <- sc defs
                                     (toClosure defaultOpts Env.empty (Ref bfc Bound v))
                                   bind ps tyArgs (S i) as sc' (Ref bfc Bound v :: vals) fvs tr
                          Right (sk, l) <- laidOut atyNF
                            | Left why => fail tr fc (Problem.ValueNotFlat !(quoteClosed atyNF) why)
                          let fv = Exp.MkFlatVar v sk l
                          sc' <- sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound v))
                          bind ps tyArgs (S i) as sc' (Ref bfc Bound v :: vals) (fv :: fvs)
                               (addVar fv !(quoteClosed atyNF) tr)
      bind ps tyArgs i [] _ vals fvs tr = pure (reverse vals, reverse fvs, tr)
      bind _ _ _ _ _ _ _ _ = fail tr fc (Problem.Unhandled "A constructor pattern of another arity")

  ||| Reduce a static term to weak head normal form, unfolding what the
  ||| translation unfolds, with the definitions the result was written inside.
  whnfStatic : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
               Tr -> ClosedTerm -> Core (ClosedTerm, List Name)
  whnfStatic tr tm
      = case getFnArgs tm of
             (Ref fc Bound x, as) =>
               case lookup x (statics !(get FlatSt)) of
                    Just (Closure t origin) =>
                      do as' <- traverse (static tr) as
                         whnfStatic (inside origin tr) (apply fc t as')
                    _ => pure (tm, tr.unfolding)
             (Bind fc _ (Lam {}) sc, a :: as) => whnfStatic tr (apply fc (subst a sc) as)
             (Bind fc _ (Let _ _ v _) sc, as) => whnfStatic tr (apply fc (subst v sc) as)
             (TForce fc _ t, []) =>
               do (TDelay _ _ _ v, origin) <- whnfStatic tr t
                    | _ => pure (tm, tr.unfolding)
                  whnfStatic (inside origin tr) v
             (Ref fc Func n, as) => whnfCall fc n False as
             (Meta fc n _ margs, as) => whnfCall fc n True (margs ++ as)
             _ => pure (tm, tr.unfolding)
    where
      -- A case tree on static values, if it selects a leaf, with the definitions
      -- the leaf was written inside.
      evalStatic : {vars : _} ->
                   Tr -> SubstEnv vars Scope.empty -> CaseTree vars ->
                   Core (Maybe (ClosedTerm, List Name))
      evalStatic tr env (STerm _ t) = pure (Just (instantiate env t, tr.unfolding))
      evalStatic tr env (Case idx p scTy alts)
          = do (v, origin) <- whnfStatic tr (Var.index env (MkVar p))
               case getFnArgs v of
                    (Ref _ (DataCon {}) cn, cargs) =>
                      do cn' <- toFullNames cn
                         conAlt cn' !(conArgs (inside origin tr) cn' cargs) alts
                    (PrimVal _ k, []) => constAlt k alts
                    _ => do tyNF <- stuckType env v scTy
                            Just _ <- Judgement.newtypeOverFunction tyNF
                              | Nothing => pure Nothing
                            Just (cn, (args ** sc)) <- pure (conCase alts)
                              | Nothing => pure Nothing
                            (vals, _, _) <- openCon tr (getLoc v) tyNF cn args (Just (v, origin))
                            let Just env' = extendSubst args vals env
                              | Nothing => pure Nothing
                            evalStatic tr env' sc
        where
          conAlt : Name -> List ClosedTerm -> List (CaseAlt vars) ->
                   Core (Maybe (ClosedTerm, List Name))
          conAlt cn cargs [] = pure Nothing
          conAlt cn cargs (ConCase n _ args sc :: as)
              = if !(toFullNames n) == cn
                   then case extendSubst args cargs env of
                             Just env' => evalStatic tr env' sc
                             Nothing => pure Nothing
                   else conAlt cn cargs as
          conAlt cn cargs (DefaultCase sc :: _) = evalStatic tr env sc
          conAlt cn cargs (_ :: as) = conAlt cn cargs as

          constAlt : Constant -> List (CaseAlt vars) -> Core (Maybe (ClosedTerm, List Name))
          constAlt k [] = pure Nothing
          constAlt k (ConstCase k' sc :: as)
              = if k == k' then evalStatic tr env sc else constAlt k as
          constAlt k (DefaultCase sc :: _) = evalStatic tr env sc
          constAlt k (_ :: as) = constAlt k as
      evalStatic tr env _ = pure Nothing

      -- A call of `n`, unfolded if it is unfoldable or a solved hole.
      whnfCall : FC -> Name -> (hole : Bool) -> List ClosedTerm -> Core (ClosedTerm, List Name)
      whnfCall fc n hole as
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                 | Nothing => pure (tm, tr.unfolding)
               fn <- toFullNames n
               marks <- staticConstants <$> get FlatSt
               case definition gdef of
                    PMDef _ targs ct _ _ =>
                      if (hole || unfoldable marks tr fn gdef) && length as >= length targs
                         then do let now = take (length targs) as
                                 Just (bs, _) <- applyType (type gdef) now
                                   | Nothing => pure (tm, tr.unfolding)
                                 now' <- staticArgs tr (zip bs now)
                                 rest <- traverse (static tr) (drop (length targs) as)
                                 let Just env = mkSubst targs now'
                                   | Nothing => pure (tm, tr.unfolding)
                                 Just (t, origin) <- evalStatic ({ unfolding $= (fn ::) } tr) env ct
                                   | Nothing => pure (tm, tr.unfolding)
                                 whnfStatic (inside origin tr) (apply fc t rest)
                         else pure (tm, tr.unfolding)
                    Builtin op =>
                      do Just k <- foldOp tr fc op as
                           | Nothing => pure (tm, tr.unfolding)
                         pure (k, tr.unfolding)
                    _ => pure (tm, tr.unfolding)

  -- A primitive operation on constants, done now.
  foldOp : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           {arity : Nat} ->
           Tr -> FC -> PrimFn arity -> List ClosedTerm -> Core (Maybe ClosedTerm)
  foldOp tr fc op as
      = do as' <- traverse (\a => fst <$> whnfStatic tr a) as
           let Just ks = the (Maybe (List Constant)) (traverse termConstant as')
             | Nothing => pure Nothing
           let Just vs = toVect arity (map (NPrimVal fc) ks)
             | Nothing => pure Nothing
           case getOp {vars = Scope.empty} op vs of
                Just (NPrimVal _ k) => pure (Just (PrimVal fc k))
                _ => pure Nothing
    where
      termConstant : ClosedTerm -> Maybe Constant
      termConstant (PrimVal _ k) = Just k
      termConstant _ = Nothing

-- The constructor information the ordinary compilation gives `cn`.
conInfo : {auto c : Ref Ctxt Defs} -> Name -> Core ConInfo
conInfo cn
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact cn (gamma defs)
           | Nothing => pure DATACON
         pure (fromFlags gdef.flags)
  where
    fromFlags : List DefFlag -> ConInfo
    fromFlags [] = DATACON
    fromFlags (ConType ci :: _) = ci
    fromFlags (_ :: fs) = fromFlags fs

-- Which of the first `arity` binders of `n`'s type are erased.
erasure : {auto c : Ref Ctxt Defs} -> Name -> Nat -> Core (List Bool)
erasure n arity
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
           | Nothing => undefinedName EmptyFC n
         go arity !(nf defs Env.empty (type gdef))
  where
    go : Nat -> ClosedNF -> Core (List Bool)
    go (S k) (NBind fc _ (Pi _ rig _ _) sc)
        = do defs <- get Ctxt
             rest <- go k !(sc defs (toClosure defaultOpts Env.empty (Erased fc Placeholder)))
             pure (isErased rig :: rest)
    go _ _ = pure []

-- The position among a constructor's run-time fields of its argument at
-- `pos`, which the ordinary compilation represents a newtype by.
newtypeField : {auto c : Ref Ctxt Defs} -> Name -> (arity : Nat) -> (pos : Nat) -> Core Nat
newtypeField cn arity pos
    = do es <- erasure cn arity
         pure (length (filter not (take pos es)))

||| The shape of the type a skeleton stands for (`Flat.Exp`): the
||| registers its values take and how ordinary code represents them, as
||| `forget` does. Nothing if the skeleton stands for no flat type, as when
||| an argument it leaves out (`SOther`) decides a field's type. A code
||| generator that lowers flat forms reads it at their boundary with
||| ordinary code, and to build and open sums.
export
shape : {auto c : Ref Ctxt Defs} -> Exp.Skeleton -> Core (Maybe Exp.Shape)
shape sk
    = do Just tm <- skeletonTerm sk
           | Nothing => pure Nothing
         defs <- get Ctxt
         typeShape !(nf defs Env.empty tm)
  where
    skeletonTerm : Exp.Skeleton -> Core (Maybe ClosedTerm)
    skeletonTerm (Exp.SPrim t) = pure (Just (PrimVal EmptyFC (PrT t)))
    skeletonTerm (Exp.SCon n as)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure Nothing
             Just as' <- sequence <$> traverse skeletonTerm as
               | Nothing => pure Nothing
             pure $ case definition gdef of
                         TCon a _ _ _ _ _ _ => Just (apply EmptyFC (Ref EmptyFC (TyCon a) n) as')
                         DCon t a _ => Just (apply EmptyFC (Ref EmptyFC (DataCon t a) n) as')
                         _ => Nothing
    skeletonTerm Exp.SOther = pure (Just (Erased EmptyFC Placeholder))

    -- The id ordinary code gives an intrinsic constructor, as
    -- `Compiler.Opts.Constructor` names and numbers them.
    intrinsicTag : ConInfo -> Maybe Int
    intrinsicTag NIL = Just 0
    intrinsicTag CONS = Just 1
    intrinsicTag NOTHING = Just 0
    intrinsicTag JUST = Just 1
    intrinsicTag _ = Nothing

    -- The judgement goes first: it rejects the recursive types, whose
    -- shapes have no end.
    mutual
      typeShape : ClosedNF -> Core (Maybe Exp.Shape)
      typeShape ty@(NPrimVal _ (PrT t))
          = do Judgement.LaidOut _ <- layout [] ty
                           | _ => pure Nothing
               pure (Just (Exp.PrimShape t))
      typeShape ty@(NTCon _ n _ args)
          = if !(toFullNames n) == Exp.uniformType then pure (Just Exp.UniformShape) else
            if !(toFullNames n) == Exp.byteAddrType then pure (Just Exp.ByteAddrShape) else
            do Judgement.LaidOut _ <- layout [] ty
                           | _ => pure Nothing
               defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                 | Nothing => pure Nothing
               Just (_, cons) <- pure (Definition.dataDeclaration (definition gdef))
                 | Nothing => pure Nothing
               cs <- traverse (conShape args) cons
               pure (Exp.DataShape <$> the (Maybe (List Exp.ConShape)) (sequence cs))
      typeShape _ = pure Nothing

      conShape : List (FC, ClosedClosure) -> Name -> Core (Maybe Exp.ConShape)
      conShape args cn
          = do defs <- get Ctxt
               Just cdef <- lookupCtxtExact cn (gamma defs)
                 | Nothing => pure Nothing
               let DCon tag arity nt = definition cdef
                 | _ => pure Nothing
               fs <- traverse (\t => typeShape !(nf defs Env.empty t))
                 !(Judgement.fieldTypes args cdef)
               let Just fs' = the (Maybe (List Exp.Shape)) (sequence fs)
                 | Nothing => pure Nothing
               ord <- case nt of
                           Just (_, pos) => Exp.AsField <$> newtypeField cn arity pos
                           Nothing => pure (ordinary tag !(conInfo cn))
               pure (Just (Exp.MkConShape !(toFullNames cn) tag ord fs'))

      -- As `Compiler.Opts.Constructor` represents a constructor that is not
      -- a newtype's.
      ordinary : Int -> ConInfo -> Exp.Ordinary
      ordinary tag (ENUM _) = Exp.AsTag
      ordinary tag ci = Exp.AsObject (fromMaybe tag (intrinsicTag ci))

-- Make the flat form of `n`, a flat function, if its signature is ground.
-- A generic one has flat forms at static arguments only. A primitive's form
-- is the primitive applied to its parameters, so that ordinary code calls it
-- as it calls any flat function; its body is not translated.
root : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
       Name -> Core ()
root n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
           | Nothing => pure ()
         fn <- toFullNames n
         sig <- signature (type gdef)
         Just (params, (rsk, rl)) <- groundSignature sig
           | Nothing => pure ()
         if fn `elem` primitives !(get FlatSt)
            then let fc = location gdef
                     vs = map fst params
                     body = Exp.FPrim fc fn rsk rl (map (\v => Exp.FVar fc v.name) vs)
                 in update FlatSt { forms $= insert fn (Exp.MkFlatDef fn vs rsk rl body fc) }
            else let tr = MkTr fn [<] (location gdef) [] empty
                 in makeForm tr (location gdef) fn fn gdef (sigPending sig.parts) params (rsk, rl)
  where
    signature : ClosedTerm -> Core Signature
    signature ty
        = do defs <- get Ctxt
             walk [] 0 [] !(nf defs Env.empty ty)
      where
        walk : (unfolded : List Name) -> Nat -> List SigPart -> ClosedNF -> Core Signature
        walk ns i acc (NBind fc x (Pi _ rig pinfo aty) sc)
            = do defs <- get Ctxt
                 v <- fresh x
                 let i' = if isExplicit pinfo then S i else i
                 let b =
                       MkApplied x rig (isAutoImplicit pinfo) (Just (i', x)) !(evalClosure defs aty)
                 walk ns i' (SigArg b v :: acc)
                      !(sc defs (toClosure defaultOpts Env.empty (Ref fc Bound v)))
        walk ns i acc res
            = do Just (n, fnTy) <- Judgement.newtypeOverFunction res
                   | Nothing => pure (MkSignature (reverse acc) res)
                 if n `elem` ns
                    then pure (MkSignature (reverse acc) res)
                    else walk (n :: ns) i (SigUnwrap :: acc) fnTy

    ||| The flat variables of a ground signature's run-time arguments, with their
    ||| types, and its result's skeleton and layout: if every run-time argument
    ||| and the result are flat. A function of any other signature has flat
    ||| forms only at static arguments: its copies.
    groundSignature : Signature ->
                      Core (Maybe (List (Exp.FlatVar, ClosedTerm), (Exp.Skeleton, Exp.Layout)))
    groundSignature sig
        = do let deferred = mapMaybe erasedVar sig.parts
             Just ps <- params deferred [] sig.parts
               | Nothing => pure Nothing
             case !(layout deferred sig.result) of
                  Judgement.LaidOut l => pure (Just (ps, (!(skeleton sig.result), l)))
                  _ => pure Nothing
      where
        erasedVar : SigPart -> Maybe Name
        erasedVar (SigArg b v) = if isErased b.rig then Just v else Nothing
        erasedVar _ = Nothing

        params : List Name -> List (Exp.FlatVar, ClosedTerm) -> List SigPart ->
                 Core (Maybe (List (Exp.FlatVar, ClosedTerm)))
        params deferred acc [] = pure (Just (reverse acc))
        params deferred acc (SigUnwrap :: ps) = params deferred acc ps
        params deferred acc (SigArg b v :: ps)
            = if isErased b.rig then params deferred acc ps else
                if b.autoImplicit then pure Nothing else
                  case !(layout deferred b.type) of
                       Judgement.LaidOut l =>
                                   do fv <- pure (Exp.MkFlatVar v !(skeleton b.type) l)
                                      params deferred ((fv, !(quoteClosed b.type)) :: acc) ps
                       _ => pure Nothing

    -- A signature's parts as what its function's case tree is applied to: the
    -- variable of each binder, and each unwrapping.
    sigPending : List SigPart -> List Pending
    sigPending = map pending
      where
        pending : SigPart -> Pending
        pending (SigArg _ v) = PArg (Ref EmptyFC Bound v)
        pending SigUnwrap = PUnwrap

    -- How many arguments a definition's type takes, erased ones included: how
    -- many a call of a primitive the directives mark takes.
    typeArity : GlobalDef -> Core Nat
    typeArity gdef
        = do defs <- get Ctxt
             go !(nf defs Env.empty (type gdef))
      where
        go : ClosedNF -> Core Nat
        go (NBind fc _ (Pi {}) sc)
            = do defs <- get Ctxt
                 S <$> go !(sc defs (toClosure defaultOpts Env.empty (Erased fc Placeholder)))
        go _ = pure Z

    ||| Make the flat form `form` of `fn`, its case tree applied to `parts`,
    ||| unless it is made or being made: `fn`'s own, or a copy of it.
    makeForm : Tr -> FC -> (form : Name) -> (fn : Name) -> GlobalDef -> (parts : List Pending) ->
               List (Exp.FlatVar, ClosedTerm) -> (Exp.Skeleton, Exp.Layout) -> Core ()
    makeForm tr fc form fn gdef parts params (rsk, rl)
        = do Nothing <- pure (lookup form (forms !(get FlatSt)))
               | Just _ => pure ()
             st <- get FlatSt
             when (not (form `elem` st.making)) $
               do let tr' = { chain := if fn == tr.root then [<] else tr.chain :< fn
                            , unfolding := [fn]
                            , vars := fromList (map (\p => ((fst p).name, p)) params)
                            } (if fn == tr.root then tr else leave tr fc)
                  let PMDef _ targs ct _ _ = definition gdef
                    | _ => fail tr' fc (Problem.Unhandled "A definition without clauses")
                  put FlatSt ({ making $= (form ::) } st)
                  let Just (envTms, pending) = takeArgs (length targs) parts
                    | Nothing =>
                      fail tr' fc (Problem.Unhandled "Clauses with more arguments than the type")
                  let Just env = mkSubst targs envTms
                    | Nothing =>
                      fail tr' fc (Problem.Unhandled "Clauses with more arguments than the type")
                  body <- trTree tr' env ct pending
                  let d = Exp.MkFlatDef form (map fst params) rsk rl body (location gdef)
                  update FlatSt { forms $= insert form d }
      where
        -- Mark `fc` as where the translation leaves the root's code, if it does.
        leave : Tr -> FC -> Tr
        leave tr EmptyFC = tr
        leave tr fc = if inRoot tr then { site := fc } tr else tr

        -- `k` arguments from the front, and what follows them.
        takeArgs : Nat -> List Pending -> Maybe (List ClosedTerm, List Pending)
        takeArgs Z ps = Just ([], ps)
        takeArgs (S k) (PArg a :: ps)
            = do (as, rest) <- takeArgs k ps
                 Just (a :: as, rest)
        takeArgs (S k) _ = Nothing

        ||| Translate a case tree, its variables bound to `env`, applied to `ps`.
        trTree : {vars : _} ->
                 Tr -> SubstEnv vars Scope.empty -> CaseTree vars -> List Pending -> Core Exp
        trTree tr env tree' ps = case tree' of
          STerm _ t => trTerm tr (instantiate env t) ps
          Unmatched msg => pure (Exp.FCrash tr.site msg)
          Impossible => pure (Exp.FCrash tr.site "Impossible case")
          Case idx p scTy alts
             => case Var.index env (MkVar p) of
                     Ref fc Bound x =>
                       case lookup x tr.vars of
                            Just (_, ty) => flatCase tr env fc x ty alts ps
                            Nothing =>
                              case lookup x (statics !(get FlatSt)) of
                                   Just _ => staticCase tr env (Ref fc Bound x) scTy alts ps
                                   Nothing => erasedCase tr env fc alts ps
                     Erased fc _ => erasedCase tr env fc alts ps
                     scr => staticCase tr env scr scTy alts ps
          where
            -- The tag a constructor of type `ty` carries in its layout: its tag if the
            -- type has several constructors.
            sumTag : ClosedNF -> Int -> Core (Maybe Int)
            sumTag (NTCon _ tn _ _) tag
                = do defs <- get Ctxt
                     Just gdef <- lookupCtxtExact tn (gamma defs)
                       | Nothing => pure Nothing
                     pure $ case Definition.dataDeclaration (definition gdef) of
                                 Just (_, _ :: _ :: _) => Just tag
                                 _ => Nothing
            sumTag _ _ = pure Nothing

            ||| Translate a closed term applied to `ps`, whose value has a flat type.
            trTerm : Tr -> ClosedTerm -> List Pending -> Core Exp
            trTerm tr tm ps
                = let (h, args) = getFnArgs tm in
                      trApp tr h (map PArg args ++ ps)
              where
                trApp : Tr -> ClosedTerm -> List Pending -> Core Exp
                trApp tr term' list = case (term', list) of
                  (Ref fc Bound x, ps)
                     => case lookup x tr.vars of
                             Just _ => case ps of
                                            [] => pure (Exp.FVar fc x)
                                            _ =>
                                              fail tr fc
                                                (Problem.Unhandled
                                                 "A flat value applied to arguments")
                             Nothing =>
                               do ps' <- traverse (staticPending tr) ps
                                  case lookup x (statics !(get FlatSt)) of
                                       Just (Closure t origin) => trTerm (inside origin tr) t ps'
                                       Just (Unwrapped v origin) =>
                                         trTerm (inside origin tr) v (PUnwrap :: ps')
                                       Nothing =>
                                         fail tr fc
                                           (Problem.Unhandled "An erased value used at run time")
                  (PrimVal fc c, []) => constant tr fc c
                  (Erased fc _, _) => pure (Exp.FNone fc)
                  (Bind fc x (Lam _ rig _ ty) sc, PArg a :: ps) => bindValue tr fc x rig ty a sc ps
                  (Bind fc x (Let _ rig v ty) sc, ps) => bindValue tr fc x rig ty v sc ps
                  (Bind fc _ (Lam {}) _, _) => fail tr fc Problem.NotStatic
                  (Bind fc _ (Pi {}) _, _) =>
                    fail tr fc (Problem.ValueNotFlat (TType fc (MN "top" 0)) Problem.RuntimeType)
                  (Ref fc (DataCon tag arity) n, ps) => conApp tr fc n tag arity ps
                  (Ref fc (TyCon _) _, _) =>
                    fail tr fc (Problem.ValueNotFlat (TType fc (MN "top" 0)) Problem.RuntimeType)
                  (Ref fc Func n, ps) => callGlobal tr fc n ps
                  (TType fc _, _) =>
                    fail tr fc (Problem.ValueNotFlat (TType fc (MN "top" 0)) Problem.RuntimeType)
                  (TForce fc _ t, ps)
                     => do (TDelay _ _ _ v, origin) <- whnfStatic tr t
                             | _ => fail tr fc Problem.NotStatic
                           ps' <- traverse (staticPending tr) ps
                           trTerm (inside origin tr) v ps'
                  (TDelay fc _ _ _, _) => fail tr fc Problem.NotStatic
                  (Meta fc n _ margs, ps)
                     => do defs <- get Ctxt
                           Just gdef <- lookupCtxtExact n (gamma defs)
                             | Nothing => undefinedName fc n
                           let PMDef _ targs ct _ _ = definition gdef
                             | _ => fail tr fc (Problem.Unhandled "An unsolved hole")
                           fn <- toFullNames n
                           unfold tr fc fn gdef ct (map PArg margs ++ ps)
                  (tm, _) => fail tr (getLoc tm) (Problem.Unhandled "This term")
                  where
                    constant : Tr -> FC -> Constant -> Core Exp
                    constant tr fc (Str _)
                        = fail tr fc
                          (Problem.ValueNotFlat (PrimVal fc (PrT StringType))
                            (Problem.BoxedPrimitive StringType))
                    constant tr fc (BI _)
                        = fail tr fc
                          (Problem.ValueNotFlat (PrimVal fc (PrT IntegerType))
                            (Problem.BoxedPrimitive IntegerType))
                    constant tr fc (PrT _) =
                      fail tr fc (Problem.ValueNotFlat (TType fc (MN "top" 0)) Problem.RuntimeType)
                    constant tr fc WorldVal = pure (Exp.FNone fc)
                    constant tr fc c = pure (Exp.FConst fc c)

                    -- Whether a binder's argument exists at run time.
                    runtime : (Applied, a) -> Bool
                    runtime (b, _) = not (isErased b.rig)

                    -- A constructor applied to `ps`: a flat value, or a newtype's function
                    -- when the context unwraps it.
                    conApp : Tr -> FC -> Name -> (tag : Int) -> (arity : Nat) -> List Pending ->
                             Core Exp
                    conApp tr fc n tag arity ps
                        = do Just (cargs, rest) <- pure (takeArgs arity ps)
                               | Nothing => fail tr fc Problem.NotStatic
                             defs <- get Ctxt
                             Just gdef <- lookupCtxtExact n (gamma defs)
                               | Nothing => undefinedName fc n
                             Just (bs, resTy) <- applyType (type gdef) cargs
                               | Nothing =>
                                 fail tr fc (Problem.Unhandled "A constructor of another arity")
                             let fields = map snd (filter runtime (zip bs cargs))
                             case rest of
                                  [] => do Right (sk, l) <- laidOut resTy
                                             | Left why =>
                                               fail tr fc
                                                 (Problem.ValueNotFlat !(quoteClosed resTy) why)
                                           fs <- traverse (\f => trTerm tr f []) fields
                                           pure
                                             (Exp.FCon fc !(toFullNames n) !(sumTag resTy tag) sk l
                                              fs)
                                  PUnwrap :: rest' =>
                                    case fields of
                                         [f] => trTerm tr f rest'
                                         _ =>
                                           fail tr fc
                                             (Problem.Unhandled "A newtype without one field")
                                  _ =>
                                    fail tr fc
                                      (Problem.Unhandled
                                       "A constructor applied to too many arguments")

                    -- The term for a translated value that is an atom.
                    atomTerm : Exp -> Maybe ClosedTerm
                    atomTerm (Exp.FVar fc x) = Just (Ref fc Bound x)
                    atomTerm (Exp.FConst fc k) = Just (PrimVal fc k)
                    atomTerm (Exp.FNone fc) = Just (Erased fc Placeholder)
                    atomTerm _ = Nothing

                    staticPending : Tr -> Pending -> Core Pending
                    staticPending tr (PArg a) = PArg <$> static tr a
                    staticPending tr p = pure p

                    -- A call of a definition that is unfolded: its case tree, at the call's
                    -- arguments. Each flat one is bound to a variable unless it is an atom, so
                    -- that it is computed once and in order, and each static one, like what
                    -- the call is applied to, is passed as a closure.
                    unfold : {targs : _} ->
                             Tr -> FC -> Name -> GlobalDef -> CaseTree targs -> List Pending ->
                             Core Exp
                    unfold tr fc fn gdef ct ps
                        = do Just (args, rest) <- pure (takeArgs (length targs) ps)
                               | Nothing => fail tr fc Problem.NotStatic
                             Just (bs, _) <- applyType (type gdef) args
                               | Nothing =>
                                 fail tr fc (Problem.Unhandled "A definition of another arity")
                             (args', wrap, tr') <- bindArgs tr fc (zip bs args)
                             rest' <- traverse (staticPending tr') rest
                             let tr'' =
                                   { unfolding $= (fn ::) }
                                     (if blockName fn then tr' else leave tr' fc)
                             let Just env = mkSubst targs args'
                               | Nothing =>
                                 fail tr fc (Problem.Unhandled "A definition of another arity")
                             wrap <$> trTree tr'' env ct rest'
                      where
                        bindArgs : Tr -> FC -> List (Applied, ClosedTerm) ->
                                   Core (List ClosedTerm, Exp -> Exp, Tr)
                        bindArgs tr fc [] = pure ([], id, tr)
                        bindArgs tr fc ((b, a) :: bas)
                            = if isErased b.rig || isAtom tr a then keep a else
                                do Right (sk, l) <- laidOut b.type
                                     | Left _ => keep !(static tr a)
                                   v <- trTerm tr a []
                                   let Nothing = atomTerm v
                                     | Just a' => keep a'
                                   x <- fresh b.name
                                   let fv = Exp.MkFlatVar x sk l
                                   (as, wrap, tr') <- bindArgs (addVar fv !(quoteClosed b.type) tr)
                                     fc bas
                                   pure (Ref fc Bound x :: as, Exp.FLet fc fv v . wrap, tr')
                          where
                            keep : ClosedTerm -> Core (List ClosedTerm, Exp -> Exp, Tr)
                            keep a' = do (as, wrap, tr') <- bindArgs tr fc bas
                                         pure (a' :: as, wrap, tr')

                    callGlobal : Tr -> FC -> Name -> List Pending -> Core Exp
                    callGlobal tr fc n ps
                        = do defs <- get Ctxt
                             Just gdef <- lookupCtxtExact n (gamma defs)
                               | Nothing => undefinedName fc n
                             fn <- toFullNames n
                             st <- get FlatSt
                             case definition gdef of
                                  Builtin op => primOp tr fc fn gdef op ps
                                  ExternDef ar => primitive tr fc fn gdef ar ps
                                  ForeignDef ar _ => primitive tr fc fn gdef ar ps
                                  PMDef _ targs ct _ _ =>
                                    if fn `elem` st.primitives
                                       then primitive tr fc fn gdef !(typeArity gdef) ps
                                    else if fn `elem` st.staticConstants
                                       then staticConstant tr fc fn gdef ps
                                    else if unfoldable st.staticConstants tr fn gdef
                                       then unfold tr fc fn gdef ct ps
                                       else demand tr fc fn gdef ps
                                  _ =>
                                    fail tr fc (Problem.Unhandled ("The reference to " ++ show fn))
                      where
                        -- The run-time arguments of a call of a primitive, which must be flat.
                        primArgs : Tr -> FC -> Name -> List (Applied, ClosedTerm) -> Core (List Exp)
                        primArgs tr fc fn bas = traverse arg (filter runtime bas)
                          where
                            arg : (Applied, ClosedTerm) -> Core Exp
                            arg (b, a)
                                = do Right _ <- laidOut b.type
                                       | Left why =>
                                         fail tr fc
                                           (Problem.CalleeNotFlat fn b.position
                                            !(quoteClosed b.type) why)
                                     trTerm tr a []

                        primOp : {arity : Nat} ->
                                 Tr -> FC -> Name -> GlobalDef -> PrimFn arity -> List Pending ->
                                 Core Exp
                        primOp tr fc fn gdef op ps
                            = do Just (args, rest) <- pure (takeArgs arity ps)
                                   | Nothing => fail tr fc Problem.NotStatic
                                 case op of
                                      Crash => crash args
                                      BelieveMe => believe args rest
                                      _ => do Nothing <- foldOp tr fc op args
                                                | Just c => trTerm tr c rest
                                              Just (bs, resTy) <- applyType (type gdef) args
                                                | Nothing =>
                                                  fail tr fc
                                                    (Problem.Unhandled
                                                     "A primitive of another arity")
                                              Right _ <- laidOut resTy
                                                | Left why =>
                                                  fail tr fc
                                                    (Problem.CalleeNotFlat fn Nothing
                                                     !(quoteClosed resTy) why)
                                              as <- primArgs tr fc fn (zip bs args)
                                              let Just vs = toVect arity as
                                                | Nothing =>
                                                  fail tr fc
                                                    (Problem.Unhandled
                                                     "A primitive of another arity")
                                              case rest of
                                                   [] => pure (Exp.FOp fc op vs)
                                                   _ =>
                                                     fail tr fc
                                                       (Problem.Unhandled
                                                         ("A primitive applied to too many " ++
                                                          "arguments"))
                          where
                            crash : List ClosedTerm -> Core Exp
                            crash [_, msg]
                                = do (PrimVal _ (Str str), _) <- whnfStatic tr msg
                                       | _ =>
                                         fail tr fc
                                           (Problem.ValueNotFlat (PrimVal fc (PrT StringType))
                                                                       (Problem.BoxedPrimitive
                                                                         StringType))
                                     pure (Exp.FCrash fc str)
                            crash _ = fail tr fc (Problem.Unhandled "A crash of another arity")

                            -- Between types of one layout, a value is its own coercion.
                            believe : List ClosedTerm -> List Pending -> Core Exp
                            believe [a, b, x] rest
                                = do defs <- get Ctxt
                                     a' <- resolved a
                                     b' <- resolved b
                                     Right (_, la) <- laidOut !(nf defs Env.empty a')
                                       | Left why => fail tr fc (Problem.ValueNotFlat a' why)
                                     Right (_, lb) <- laidOut !(nf defs Env.empty b')
                                       | Left why => fail tr fc (Problem.ValueNotFlat b' why)
                                     if la == lb
                                        then trTerm tr x rest
                                        else fail tr fc
                                          (Problem.Unhandled "A coercion between layouts")
                            believe _ _ =
                              fail tr fc (Problem.Unhandled "A coercion of another arity")

                        -- An `%extern` or `%foreign` primitive, or one of the backend's: a
                        -- definition its directive marks, whose body the translation leaves.
                        primitive : Tr -> FC -> Name -> GlobalDef -> (arity : Nat) ->
                                    List Pending -> Core Exp
                        primitive tr fc fn gdef arity ps
                            = do Just (args, rest) <- pure (takeArgs arity ps)
                                   | Nothing => fail tr fc Problem.NotStatic
                                 checkPrivate tr fc fn gdef
                                 Just (bs, resTy) <- applyType (type gdef) args
                                   | Nothing =>
                                     fail tr fc (Problem.Unhandled "A primitive of another arity")
                                 Right (sk, lay) <- laidOut resTy
                                   | Left why =>
                                     fail tr fc
                                       (Problem.CalleeNotFlat fn Nothing !(quoteClosed resTy) why)
                                 as <- primArgs tr fc fn (zip bs args)
                                 case rest of
                                      [] => pure (Exp.FPrim fc fn sk lay as)
                                      _ =>
                                        fail tr fc
                                          (Problem.Unhandled
                                           "A primitive applied to too many arguments")
                          where
                            -- A private primitive is used only where its own module wrote it: the
                            -- definition the reference was written inside, the innermost being
                            -- unfolded or translated, is in the primitive's own source file.
                            checkPrivate : Tr -> FC -> Name -> GlobalDef -> Core ()
                            checkPrivate tr fc fn gdef
                                = when (collapseDefault (visibility gdef) == Private) $
                                    do defs <- get Ctxt
                                       Just writer <- pure (head' tr.unfolding)
                                         | Nothing => fail tr fc (Problem.PrivateElsewhere fn)
                                       Just wdef <- lookupCtxtExact writer (gamma defs)
                                         | Nothing => fail tr fc (Problem.PrivateElsewhere fn)
                                       case (origin (location wdef), origin (location gdef)) of
                                            (Just here, Just home) => unless (here == home) $
                                              fail tr fc (Problem.PrivateElsewhere fn)
                                            _ => fail tr fc (Problem.PrivateElsewhere fn)
                              where
                                origin : FC -> Maybe OriginDesc
                                origin (MkFC o _ _) = Just o
                                origin (MkVirtualFC o _ _) = Just o
                                origin EmptyFC = Nothing

                        -- A call of a function that is not unfolded: a call of its flat form, or,
                        -- at static arguments, of its copy at them.
                        demand : Tr -> FC -> Name -> GlobalDef -> List Pending -> Core Exp
                        demand tr fc fn gdef ps
                            = do sig <- signature (type gdef)
                                 Just (params, res) <- groundSignature sig
                                   | Nothing => copy tr fc fn gdef ps
                                 let args = mapMaybe pendingArg ps
                                 let erasure = mapMaybe binderErased sig.parts
                                 when (length args /= length erasure) $ fail tr fc Problem.NotStatic
                                 as <- traverse (\a => trTerm tr a [])
                                   (map fst (filter (not . snd) (zip args erasure)))
                                 makeForm tr fc fn fn gdef (sigPending sig.parts) params res
                                 pure (Exp.FCall fc fn as)
                          where
                            binderErased : SigPart -> Maybe Bool
                            binderErased (SigArg b _) = Just (isErased b.rig)
                            binderErased _ = Nothing

                            pendingArg : Pending -> Maybe ClosedTerm
                            pendingArg (PArg a) = Just a
                            pendingArg _ = Nothing

                            -- A call of `fn` at static arguments: a call of its copy at them, made
                            -- on demand and memoised by the function and its static arguments.
                            --
                            -- The callee's type is walked with the call's arguments, which
                            -- instantiate the types of the binders after them. An argument is
                            -- static if its binder is erased or auto-implicit, if its type's values
                            -- are static only (a function, a type, a lazy value, a dictionary), or
                            -- if it is closed and its type has no layout (a message to
                            -- `idris_crash`); it is substituted into the copy's case tree. Any
                            -- other argument of a flat type is dynamic, a parameter of the copy.
                            -- The flat variables the static arguments capture, such as those a
                            -- lambda refers to, are parameters too, after the dynamic ones, renamed
                            -- in the copy so that one copy serves every call whose static arguments
                            -- are the same terms.
                            copy : Tr -> FC -> Name -> GlobalDef -> List Pending -> Core Exp
                            copy tr fc fn gdef ps
                                = do defs <- get Ctxt
                                     (parts, params, actuals, res) <- walk [] 0
                                       (mapMaybe pendingArg ps)
                                                                          !(nf defs Env.empty
                                                                            (type gdef))
                                                                            [<] [<] [<]
                                     Right res' <- laidOut res
                                       | Left why =>
                                         fail tr fc
                                           (Problem.CalleeNotFlat fn Nothing !(quoteClosed res) why)
                                     -- the flat variables the static arguments capture
                                     sts <- statics <$> get FlatSt
                                     let staticTerms = mapMaybe pendingStatic parts
                                     let caps = filter (\x => isJust (lookup x tr.vars))
                                                       (nub
                                                         (Data.Builder.joinMap
                                                           (boundRefs . substLets . resolve sts)
                                                          staticTerms))
                                     let canon =
                                           zip caps
                                             (map (MN "flat captured" . cast) [0 .. length caps])
                                     parts' <- relocateParts (fromList canon) parts
                                     key <- traverse pendingKey parts'
                                     as <- traverse (\a => trTerm tr a []) actuals
                                     let capArgs = map (Exp.FVar fc) caps
                                     st <- get FlatSt
                                     case find (\cp => cp.function == fn && sameKey cp.key key)
                                       st.copies of
                                          Just cp => pure (Exp.FCall fc cp.form (as ++ capArgs))
                                          Nothing =>
                                            do when (count (== fn) (tr.chain <>> []) >= copyDepth) $
                                                 fail tr fc (Problem.CopiesDoNotEnd fn)
                                               name <- pure (copyName fn st.nextName)
                                               update FlatSt
                                                 { nextName $= (+ 1), copies $= (MkCopy fn key name
                                                                                 ::) }
                                               capParams <- traverse (capParam canon) caps
                                               makeForm tr fc name fn gdef (map snd parts')
                                                 (params ++ capParams) res'
                                               pure (Exp.FCall fc name (as ++ capArgs))
                              where
                                -- The `Bound` names a term refers to, in the order it first refers
                                -- to them.
                                boundRefs : Term vars'' -> List Name
                                boundRefs tm = nub (toList (go tm))
                                  where
                                    -- The terms a binder holds.
                                    binderTerms : Binder (Term vars') -> List (Term vars')
                                    binderTerms (Lam _ _ _ ty) = [ty]
                                    binderTerms (Let _ _ v ty) = [v, ty]
                                    binderTerms (Pi _ _ _ ty) = [ty]
                                    binderTerms (PVar _ _ _ ty) = [ty]
                                    binderTerms (PLet _ _ v ty) = [v, ty]
                                    binderTerms (PVTy _ _ ty) = [ty]

                                    go : Term vs -> Data.Builder Name
                                    go (Ref _ Bound x) = Data.Builder.single x
                                    -- lint: allow trust-escape: a binder's terms are parts of it,
                                    -- which `binderTerms` hides
                                    go (Bind _ _ b sc) = concatMap go (assert_total (binderTerms b))
                                      <+> go sc
                                    go (App _ f a) = go f <+> go a
                                    go (As _ _ a p) = go a <+> go p
                                    go (TDelayed _ _ t) = go t
                                    go (TDelay _ _ t v) = go t <+> go v
                                    go (TForce _ _ t) = go t
                                    go (Meta _ _ _ args) = concatMap go args
                                    go _ = neutral

                                closed : ClosedTerm -> Bool
                                closed t = all (\x => isNothing (lookup x tr.vars)) (boundRefs t)

                                -- Whether a reason for a type not to be flat makes its values
                                -- static only: a function, a type, a lazy value, or something
                                -- holding one, such as a dictionary. An argument of such a type is
                                -- always a static argument, which a flat form at it takes. Any
                                -- other type without a layout, such as `String`, has values
                                -- computed at run time, and makes the callee not flat.
                                staticOnly : Problem.NotFlatReason -> Bool
                                staticOnly Problem.FunctionType = True
                                staticOnly Problem.RuntimeType = True
                                staticOnly Problem.LazyType = True
                                staticOnly (Problem.InField _ _ _ why) = staticOnly why
                                staticOnly _ = False

                                -- Each part: what the case tree is applied to, and whether it is
                                -- static (`True`, an argument the key holds) or not. The parts, the
                                -- parameters and the actual arguments accumulate at their ends, an
                                -- argument at a time.
                                walk : (unfolded : List Name) -> (explicit : Nat) ->
                                       List ClosedTerm -> ClosedNF ->
                                       SnocList (Bool, Pending) ->
                                       SnocList (Exp.FlatVar, ClosedTerm) ->
                                       SnocList ClosedTerm ->
                                       Core (List (Bool, Pending),
                                             List (Exp.FlatVar, ClosedTerm), List ClosedTerm,
                                             ClosedNF)
                                walk ns i (a :: as) (NBind bfc x (Pi _ rig pinfo aty) sc) parts
                                  params actuals
                                    = do defs <- get Ctxt
                                         let i' = if isExplicit pinfo then S i else i
                                         tyNF <- evalClosure defs aty
                                         a' <- resolved a
                                         let next : ClosedTerm -> Core ClosedNF
                                                   = \t =>
                                                     sc defs (toClosure defaultOpts Env.empty t)
                                         if isErased rig
                                            then walk ns i' as !(next a') (parts :< (True, PArg a))
                                              params actuals
                                            else if isAutoImplicit pinfo
                                              then do sa <- static tr a
                                                      walk ns i' as !(next a')
                                                        (parts :< (True, PArg sa)) params actuals
                                              else case !(layout [] tyNF) of
                                                Judgement.LaidOut l =>
                                                            do v <- fresh x
                                                               fv <- pure
                                                                 (Exp.MkFlatVar v !(skeleton tyNF)
                                                                  l)
                                                               walk ns i' as
                                                                 !(next (Ref bfc Bound v))
                                                                 (parts :<
                                                                   (False, PArg (Ref bfc Bound v)))
                                                                    (params :<
                                                                      (fv, !(quoteClosed tyNF)))
                                                                      (actuals :< a)
                                                Judgement.Rejected why =>
                                                            let a'' = deadLets a' in
                                                            if staticOnly why || closed a''
                                                               then do sa <- static tr a''
                                                                       walk ns i' as !(next a')
                                                                         (parts :< (True, PArg sa))
                                                                           params actuals
                                                               else fail tr fc
                                                                 (Problem.CalleeNotFlat fn
                                                                   (Just (i', x))
                                                                  !(quoteClosed tyNF) why)
                                                Judgement.Deferred =>
                                                  fail tr fc
                                                    (Problem.Unhandled
                                                      "A type made of erased arguments at a call")
                                walk ns i as res parts params actuals
                                    = do Just (n, fnTy) <- Judgement.newtypeOverFunction res
                                           | Nothing => done
                                         if elem n ns || isNil as then done
                                            else walk (n :: ns) i as fnTy
                                              (parts :< (False, PUnwrap)) params actuals
                                  where
                                    done : Core (List (Bool, Pending),
                                                 List (Exp.FlatVar, ClosedTerm), List ClosedTerm,
                                                 ClosedNF)
                                    done = if isNil as
                                      then pure (parts <>> [], params <>> [], actuals <>> [], res)
                                      else fail tr fc Problem.NotStatic

                                pendingStatic : (Bool, Pending) -> Maybe ClosedTerm
                                pendingStatic (True, PArg t) = Just t
                                pendingStatic _ = Nothing

                                -- A term with every let substituted into its scope.
                                substLets : Term vars'' -> Term vars''
                                substLets (Bind fc x (Let _ _ v _) sc) = substLets (subst v sc)
                                substLets (Bind fc x b sc) =
                                  Bind fc x (map substLets b) (substLets sc)
                                substLets (App fc f a) = App fc (substLets f) (substLets a)
                                substLets (As fc u a p) = As fc u (substLets a) (substLets p)
                                substLets (TDelayed fc r t) = TDelayed fc r (substLets t)
                                substLets (TDelay fc r t v) =
                                  TDelay fc r (substLets t) (substLets v)
                                substLets (TForce fc r t) = TForce fc r (substLets t)
                                substLets (Meta fc n i args) = Meta fc n i (map substLets args)
                                substLets tm = tm

                                ||| Terms that are static arguments of a copy, with the flat
                                ||| variables they capture renamed by `caps`. A name that stands for
                                ||| a static value whose term captures one, directly or through
                                ||| another such name, stands for a renamed copy of it, written
                                ||| where the original was, so that each copy sees only its own
                                ||| parameters.
                                relocate : (caps : NameMap Name) -> List ClosedTerm ->
                                           Core (List ClosedTerm)
                                relocate caps ts
                                    = do sts <- statics <$> get FlatSt
                                         let moved =
                                               filter (captures sts [])
                                                 (nub (toList (concatMap (reachable sts []) ts)))
                                         renames <- traverse (\x => pure (x, !(fresh x))) moved
                                         let m =
                                               foldl (\acc, (x, x') => insert x x' acc) caps renames
                                         traverse_ (copied sts m) renames
                                         pure (map (renameRefs m) ts)
                                  where
                                    -- The term a static value stands for.
                                    staticTerm : Static -> ClosedTerm
                                    staticTerm (Closure t _) = t
                                    staticTerm (Unwrapped v _) = v

                                    -- The names standing for static values that a term reaches.
                                    -- Through lets, as a key looks: a let is a substitution, and
                                    -- one that Idris binds around a case alternative's right-hand
                                    -- side names the alternative's variables without the static
                                    -- term capturing them.
                                    reachable : NameMap Static -> List Name -> Term vs ->
                                                Data.Builder Name
                                    reachable sts seen tm
                                        = concatMap (\x => if elem x seen then neutral else
                                                             case lookup x sts of
                                                                  Just st => Data.Builder.single x
                                                                    <+> reachable sts (x :: seen)
                                                                      (staticTerm st)
                                                                  Nothing => neutral)
                                                    (boundRefs (substLets tm))

                                    captures : NameMap Static -> List Name -> Name -> Bool
                                    captures sts seen x
                                        = case lookup x sts of
                                               Nothing => False
                                               Just st => any (\y => isJust (lookup y caps)
                                                                     ||
                                                                       (not (elem y seen)
                                                                        && captures sts (x :: seen)
                                                                          y))
                                                              (boundRefs
                                                                (substLets (staticTerm st)))

                                    -- A term with `Bound` names renamed.
                                    renameRefs : NameMap Name -> Term vars'' -> Term vars''
                                    renameRefs m (Ref fc Bound x) =
                                      Ref fc Bound (fromMaybe x (lookup x m))
                                    renameRefs m (Bind fc x b sc) =
                                      Bind fc x (map (renameRefs m) b) (renameRefs m sc)
                                    renameRefs m (App fc f a) =
                                      App fc (renameRefs m f) (renameRefs m a)
                                    renameRefs m (As fc u a p) =
                                      As fc u (renameRefs m a) (renameRefs m p)
                                    renameRefs m (TDelayed fc r t) = TDelayed fc r (renameRefs m t)
                                    renameRefs m (TDelay fc r t v) =
                                      TDelay fc r (renameRefs m t) (renameRefs m v)
                                    renameRefs m (TForce fc r t) = TForce fc r (renameRefs m t)
                                    renameRefs m (Meta fc n i args) =
                                      Meta fc n i (map (renameRefs m) args)
                                    renameRefs m tm = tm

                                    renameStatic : NameMap Name -> Static -> Static
                                    renameStatic m (Closure t o) = Closure (renameRefs m t) o
                                    renameStatic m (Unwrapped v o) = Unwrapped (renameRefs m v) o

                                    -- A static value moved to its fresh name, its references
                                    -- renamed.
                                    copied : NameMap Static -> NameMap Name -> (Name, Name) ->
                                             Core ()
                                    copied sts m (x, x') = case lookup x sts of
                                      Just st =>
                                        update FlatSt { statics $= insert x' (renameStatic m st) }
                                      Nothing => pure ()

                                relocateParts : NameMap Name -> List (Bool, Pending) ->
                                                Core (List (Bool, Pending))
                                relocateParts canon parts
                                    = do moved <- relocate canon (mapMaybe pendingStatic parts)
                                         pure (place parts moved)
                                  where
                                    place : List (Bool, Pending) -> List ClosedTerm ->
                                            List (Bool, Pending)
                                    place ((True, PArg _) :: ps') (t :: ts) = (True, PArg t)
                                      :: place ps' ts
                                    place (p :: ps') ts = p :: place ps' ts
                                    place [] _ = []

                                -- A let is a substitution, so a key sees through it: inside a case
                                -- alternative Idris binds the matched variable to its value with
                                -- one, around the whole right-hand side, and a recursive call there
                                -- would otherwise carry one more let per level and never meet its
                                -- memo.
                                pendingKey : (Bool, Pending) -> Core (Maybe ClosedTerm)
                                pendingKey (True, PArg t) =
                                  Just <$> toFullNames (substLets !(resolved t))
                                pendingKey _ = pure Nothing

                                sameKey : List (Maybe ClosedTerm) -> List (Maybe ClosedTerm) -> Bool
                                sameKey [] [] = True
                                sameKey (Nothing :: ks) (Nothing :: ks') = sameKey ks ks'
                                sameKey (Just t :: ks) (Just t' :: ks') = eqTerm t t'
                                  && sameKey ks ks'
                                sameKey _ _ = False

                                capParam : List (Name, Name) -> Name ->
                                           Core (Exp.FlatVar, ClosedTerm)
                                capParam canon x
                                    = do Just (fv, ty) <- pure (lookup x tr.vars)
                                           | Nothing =>
                                             fail tr fc
                                               (Problem.Unhandled
                                                "A captured variable out of scope")
                                         pure ({ name := fromMaybe fv.name (lookup x canon) } fv,
                                               ty)

                                -- The name of the form of a copy of `fn`.
                                copyName : Name -> Int -> Name
                                copyName (NS ns n) k = NS ns (copyName n k)
                                copyName (DN _ n) k = copyName n k
                                copyName n k = MN (nameRoot n) k

                                -- How many copies of one function may nest in a chain of calls
                                -- before its static arguments count as growing without end. Only
                                -- recursion at other static arguments nests them, and such
                                -- arguments, and the types they decide, can double at each step, so
                                -- the bound is small.
                                copyDepth : Nat
                                copyDepth = 8

                        -- A constant the program marks static, at its erased arguments:
                        -- its value, which the code generator computes as it compiles the
                        -- program, if flat code holds it as ordinary code holds it, in one
                        -- uniform register, or if it is a machine scalar; else a call of
                        -- its form, which computes it. One applied to a run-time argument
                        -- is no constant, and stops the translation.
                        staticConstant : Tr -> FC -> Name -> GlobalDef -> List Pending -> Core Exp
                        staticConstant tr fc fn gdef ps
                            = do let (args, rest) = spanArgs ps
                                 Just (bs, resTy) <- applyType (type gdef) args
                                   | Nothing => demand tr fc fn gdef ps
                                 when (any (\b => not (isErased b.rig)) bs) $
                                   fail tr fc
                                     (Problem.Unhandled
                                       "A constant marked static, applied to run-time arguments,")
                                 Right (sk, lay) <- laidOut resTy
                                   | Left _ => demand tr fc fn gdef ps
                                 held <- case sk of
                                   Exp.SPrim _ => pure True
                                   _ => do sh <- shape sk
                                           pure (lay == [Rep.Uniform]
                                                 && maybe False Exp.heldAsUniform sh)
                                 if held && null rest
                                    then pure (Exp.FStatic fc fn sk lay)
                                    else demand tr fc fn gdef ps
                          where
                            -- the arguments in front, and what follows them
                            spanArgs : List Pending -> (List ClosedTerm, List Pending)
                            spanArgs (PArg a :: ps') = let (as, rest) = spanArgs ps' in
                                                         (a :: as, rest)
                            spanArgs ps' = ([], ps')

                    -- `let x = v in sc`, or `(\x => sc) v`, in one body: a flat value is bound
                    -- to a variable unless it is an atom, and a static one is substituted.
                    bindValue : Tr -> FC -> (x : Name) -> RigCount -> (ty : ClosedTerm) ->
                                (v : ClosedTerm) -> Term [x] -> List Pending -> Core Exp
                    bindValue tr fc x rig ty v sc ps
                        = if isErased rig || isAtom tr v then trTerm tr (subst v sc) ps else
                            do defs <- get Ctxt
                               ty' <- resolved ty
                               tyNF <- nf defs Env.empty ty'
                               -- Idris leaves the type out of a `let` whose type it inferred:
                               -- then the value's own, as its form shows
                               let NErased _ _ = tyNF
                                 | _ => do Right (sk, l) <- laidOut tyNF
                                             | Left _ => trTerm tr (subst v sc) ps
                                           v' <- trTerm tr v []
                                           bindFlat sk l v'
                               v' <- trTerm tr v []
                               sts <- get FlatSt
                               let Just (sk, l) = Exp.expType (varType tr) (formType sts) v'
                                 | Nothing =>
                                   fail tr fc (Problem.Unhandled "A let whose type is not known")
                               bindFlat sk l v'
                      where
                        varType : Tr -> Name -> Maybe (Exp.Skeleton, Exp.Layout)
                        varType tr y = (\(fv, _) => (fv.skeleton, fv.layout)) <$> lookup y tr.vars

                        formType : FlatState -> Name -> Maybe (Exp.Skeleton, Exp.Layout)
                        formType sts n =
                          (\fd => (fd.resultSkeleton, fd.result)) <$> lookup n sts.forms

                        -- the value bound to a fresh flat variable, unless it is an atom
                        bindFlat : Exp.Skeleton -> Exp.Layout -> Exp -> Core Exp
                        bindFlat sk l v'
                            = do let Nothing = atomTerm v'
                                   | Just a => trTerm tr (subst a sc) ps
                                 x' <- fresh x
                                 let fv = Exp.MkFlatVar x' sk l
                                 body <- trTerm (addVar fv !(resolved ty) tr)
                                   (subst (Ref fc Bound x') sc) ps
                                 pure (Exp.FLet fc fv v' body)

            -- A case on a flat variable: a case at run time.
            flatCase : {vars' : _} ->
                       Tr -> SubstEnv vars' Scope.empty -> FC -> Name -> ClosedTerm ->
                       List (CaseAlt vars') -> List Pending -> Core Exp
            flatCase tr env fc x ty alts ps
                = do defs <- get Ctxt
                     tyNF <- nf defs Env.empty ty
                     (cas, def) <- go tyNF alts
                     pure (Exp.FCase fc (Exp.FVar fc x) cas def)
              where
                go : ClosedNF -> List (CaseAlt vars') -> Core (List Exp.FlatAlt, Maybe Exp)
                go tyNF [] = pure ([], Nothing)
                go tyNF (ConCase cn tag args sc :: as)
                    = do (vals, fvs, tr') <- openCon tr fc tyNF cn args Nothing
                         let Just env' = extendSubst args vals env
                           | Nothing =>
                             fail tr fc (Problem.Unhandled "A constructor pattern of another arity")
                         body <- trTree tr' env' sc ps
                         (rest, def) <- go tyNF as
                         pure (Exp.FConAlt !(toFullNames cn) !(sumTag tyNF tag) fvs body :: rest,
                               def)
                go tyNF (ConstCase k sc :: as)
                    = do body <- trTree tr env sc ps
                         (rest, def) <- go tyNF as
                         pure (Exp.FConstAlt k body :: rest, def)
                go tyNF (DefaultCase sc :: _)
                    = do body <- trTree tr env sc ps
                         pure ([], Just body)
                go tyNF (DelayCase {} :: _) = fail tr fc (Problem.ValueNotFlat ty Problem.LazyType)

            -- A case on an erased value, which the run-time tree does not have: the
            -- case has one alternative.
            erasedCase : {vars' : _} ->
                         Tr -> SubstEnv vars' Scope.empty -> FC -> List (CaseAlt vars') ->
                         List Pending -> Core Exp
            erasedCase tr env fc [ConCase _ _ args sc] ps
                = do vals <- traverse (\a => Ref fc Bound <$> fresh a) args
                     let Just env' = extendSubst args vals env
                       | Nothing =>
                         fail tr fc (Problem.Unhandled "A constructor pattern of another arity")
                     trTree tr env' sc ps
            erasedCase tr env fc [DefaultCase sc] ps = trTree tr env sc ps
            erasedCase tr env fc _ ps = fail tr fc (Problem.Unhandled "A case on an erased value")

            -- A case on a static value: the alternative it selects. A value of a
            -- newtype over a function that does not reduce selects the newtype's
            -- constructor, its function unwrapped.
            staticCase : {vars' : _} ->
                         Tr -> SubstEnv vars' Scope.empty -> ClosedTerm -> Term vars' ->
                         List (CaseAlt vars') -> List Pending -> Core Exp
            staticCase tr env scr scTy alts ps
                = do (v, origin) <- whnfStatic tr scr
                     case getFnArgs v of
                          (Ref _ (DataCon {}) cn, cargs) =>
                            do cn' <- toFullNames cn
                               conAlt cn' !(conArgs (inside origin tr) cn' cargs) alts
                          (PrimVal _ k, []) => constAlt k alts
                          _ => do tyNF <- stuckType env v scTy
                                  Just _ <- Judgement.newtypeOverFunction tyNF
                                    | Nothing => do Right _ <- laidOut tyNF
                                                      | Left why =>
                                                        fail tr (getLoc scr)
                                                          (Problem.ValueNotFlat !(quoteClosed tyNF)
                                                            why)
                                                    fail tr (getLoc scr)
                                                      (Problem.Unhandled
                                                        "A case on a value that is not a variable")
                                  Just (cn, (args ** sc)) <- pure (conCase alts)
                                    | Nothing => fail tr (getLoc scr) Problem.NotStatic
                                  (vals, _, tr') <- openCon tr (getLoc scr) tyNF cn args
                                    (Just (v, origin))
                                  let Just env' = extendSubst args vals env
                                    | Nothing =>
                                      fail tr (getLoc scr)
                                        (Problem.Unhandled "A constructor pattern of another arity")
                                  trTree tr' env' sc ps
              where
                conAlt : Name -> List ClosedTerm -> List (CaseAlt vars') -> Core Exp
                conAlt cn cargs [] = pure (Exp.FCrash (getLoc scr) "Unmatched case")
                conAlt cn cargs (ConCase n _ args sc :: as)
                    = if !(toFullNames n) == cn
                         then do let Just env' = extendSubst args cargs env
                                   | Nothing =>
                                     fail tr (getLoc scr)
                                       (Problem.Unhandled "A constructor pattern of another arity")
                                 trTree tr env' sc ps
                         else conAlt cn cargs as
                conAlt cn cargs (DefaultCase sc :: _) = trTree tr env sc ps
                conAlt cn cargs (_ :: as) = conAlt cn cargs as

                constAlt : Constant -> List (CaseAlt vars') -> Core Exp
                constAlt k [] = pure (Exp.FCrash (getLoc scr) "Unmatched case")
                constAlt k (ConstCase k' sc :: as)
                    = if k == k' then trTree tr env sc ps else constAlt k as
                constAlt k (DefaultCase sc :: _) = trTree tr env sc ps
                constAlt k (_ :: as) = constAlt k as

||| The definitions a code generator's directives of a mark name
||| (`Problem.Mark`): each directive of the mark's word followed by names,
||| each as written in the program, qualified as far as it takes to name one
||| definition. A name that names none, or more than one, is an error.
export
markedNames : {auto c : Ref Ctxt Defs} -> Problem.Mark -> (directives : List String) ->
              Core (List Name, List Problem.FlatError)
markedNames mark directives
    = do -- Idris gives a module's directives last first
         found <- traverse one (nub (Data.Builder.joinMap names (reverse directives)))
         pure (nub (mapMaybe ok found), mapMaybe bad found)
  where
    names : String -> List String
    names d = case words d of
                   (w :: ns) => if w == Problem.directive mark then ns else []
                   [] => []

    -- An operator is written in parentheses, as in a program; its name has
    -- none.
    basic : String -> Name
    basic n = UN (Basic (if isPrefixOf "(" n && isSuffixOf ")" n
                            then substr 1 (minus (length n) 2) n
                            else n))

    parsed : String -> Name
    parsed str = case reverse (forget (split (== '.') str)) of
                      [n] => basic n
                      (n :: ns) =>
                        NS (mkNamespace (concat (intersperse "." (reverse ns)))) (basic n)
                      [] => basic str

    one : String -> Core (Either Problem.FlatError Name)
    one str
        = do defs <- get Ctxt
             found <- lookupCtxtName (parsed str) (gamma defs)
             case found of
                  [(n, _, _)] => Right <$> toFullNames n
                  ms =>
                    pure
                      (Left
                       (Problem.UnknownMarkedName mark str
                         !(traverse (\(n, _, _) => toFullNames n) ms)))

    ok : Either Problem.FlatError Name -> Maybe Name
    ok (Right n) = Just n
    ok _ = Nothing

    bad : Either Problem.FlatError Name -> Maybe Problem.FlatError
    bad (Left e) = Just e
    bad _ = Nothing

||| The flat forms of the flat functions given, and of the ground functions
||| they call, with the errors of those that have none: a signature that is
||| not flat, or a body. A function that fails leaves no forms behind, of its
||| own or of its callees. A call of one of the backend's primitives, which
||| the code generator names (`primitives`), is the primitive's, and each
||| primitive given has the form that applies it. A read of a constant the
||| program marks static (`staticConstants`) is its value (`FStatic`) where
||| flat code holds that as ordinary code does, in one uniform register, or
||| as a machine scalar; else a call of its form.
export
flatForms : {auto c : Ref Ctxt Defs} -> (primitives, staticConstants : List Name) -> List Name ->
            Core (NameMap Exp.FlatDef, List Problem.FlatError)
flatForms primitives staticConstants ns
    = do s <- newRef FlatSt (MkFlatState primitives staticConstants 0 [] empty empty [] Nothing)
         errs <- catMaybes <$> traverse tryRoot ns
         pure ((forms !(get FlatSt)), errs)
  where
    tryRoot : {auto s : Ref FlatSt FlatState} -> Name -> Core (Maybe Problem.FlatError)
    tryRoot n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure Nothing
             Nothing <- Judgement.checkFlatSignature (location gdef) n
               | err => pure err
             before <- get FlatSt
             catch (do root n; pure Nothing)
                   (\err => do st <- get FlatSt
                               put FlatSt
                                 ({ forms := forms before, making := [], failure := Nothing } st)
                               case failure st of
                                    Just e => pure (Just e)
                                    Nothing => throw err)

||| Whether a flat form of the name and the number of parameters is a copy at
||| static arguments of none left: a copy is of a machine name
||| (`copyName`), and called by flat forms alone, never by ordinary code.
unparameterised : Name -> (params : Nat) -> Bool
unparameterised (NS _ n) k = unparameterised n k
unparameterised (MN _ _) Z = True
unparameterised _ _ = False

||| The ordinary form of a flat form: every value represented as ordinary code
||| represents it, every call by name, taking the definition's run-time
||| arguments as ordinary code passes them. It witnesses that the flat regime
||| is part of the ordinary one, and is the flat translation's test oracle.
||| Like every compiled form, it then has its constructors specialised
||| (`Compiler.Opts.Constructor`). A copy at static arguments of no
||| parameters left (`unparameterised`) takes one, erased, which each call
||| of it passes: a definition of no arguments is a constant to the Scheme
||| code generators, which evaluate it before the program runs, so a crash
||| on a branch the program never takes would end it at its start.
export
forget : {auto c : Ref Ctxt Defs} -> Exp.FlatDef -> Core CDef
forget d
    = do let args = if unparameterised d.name (length d.params)
                      then [MN "unparameterised" 0] else map name d.params
         s <- newRef NextMN 0
         constructorCDef (MkFun args !(forgetExp {vars = args} d.body))
  where
    forgetExp : {vars : _} -> Exp -> Core (CExp vars)
    forgetExp (Exp.FVar fc x)
        = case isVar x vars of
               Just (MkVar p) => pure (CLocal fc p)
               Nothing => throw (InternalError ("Flat form with an unbound variable " ++ show x))
    forgetExp (Exp.FLet fc v val sc)
        = pure (CLet fc v.name NotInline !(forgetExp val) !(forgetExp {vars = v.name :: vars} sc))
    forgetExp (Exp.FConst fc k) = pure (CPrimVal fc k)
    forgetExp (Exp.FOp fc op as) = COp fc op <$> forgetArgs as
      where
        forgetArgs : {vars' : _} -> Vect n Exp -> Core (Vect n (CExp vars'))
        forgetArgs [] = pure []
        forgetArgs (a :: as) = pure (!(forgetExp a) :: !(forgetArgs as))
    forgetExp (Exp.FCall fc n as) =
      if unparameterised n (length as) then pure (CApp fc (CRef fc n) [CErased fc])
        else CApp fc (CRef fc n) <$> traverse forgetExp as
    forgetExp (Exp.FPrim fc n _ _ as)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => undefinedName fc n
             let arity = case definition gdef of
                              ExternDef a => a
                              ForeignDef a _ => a
                              _ => length as
             CApp fc (CRef fc n) <$> withErased fc !(erasure n arity) !(traverse forgetExp as)
      where
        -- The arguments of a primitive's call, the erased ones as `CErased`.
        withErased : FC -> List Bool -> List (CExp vars') -> Core (List (CExp vars'))
        withErased fc (True :: es) as = (CErased fc ::) <$> withErased fc es as
        withErased fc (False :: es) (a :: as) = (a ::) <$> withErased fc es as
        withErased fc _ as = pure as
    -- a constant marked static is the constant, which the Scheme code
    -- generators compute before the program runs
    forgetExp (Exp.FStatic fc n _ _) = pure (CApp fc (CRef fc n) [])
    forgetExp (Exp.FCon fc cn _ _ _ as)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact cn (gamma defs)
               | Nothing => undefinedName fc cn
             as' <- traverse forgetExp as
             case definition gdef of
                  DCon _ arity (Just (_, pos)) =>
                    do Just a <- pure (atIndex !(newtypeField cn arity pos) as')
                         | Nothing =>
                           throw
                             (InternalError ("Flat form with a newtype of no field: " ++ show cn))
                       pure a
                  DCon tag _ _ => pure (CCon fc cn !(conInfo cn) (Just tag) as')
                  _ =>
                    throw
                      (InternalError ("Flat form with a constructor that is not one: " ++ show cn))
      where
        atIndex : Nat -> List a -> Maybe a
        atIndex _ [] = Nothing
        atIndex Z (x :: _) = Just x
        atIndex (S k) (_ :: xs) = atIndex k xs
    forgetExp (Exp.FCase fc scr alts def)
        = do scr' <- forgetExp scr
             def' <- traverseOpt forgetExp def
             case alts of
                  [] => pure (fromMaybe (CCrash fc "No alternative") def')
                  (Exp.FConstAlt {} :: _) =>
                    pure (CConstCase fc scr' !(traverse constAlt alts) def')
                  [Exp.FConAlt cn _ fvs sc] =>
                        do Just k <- newtype cn
                             | Nothing => pure (CConCase fc scr' !(traverse conAlt alts) def')
                           unwrap (Just k) fvs sc
                  _ => pure (CConCase fc scr' !(traverse conAlt alts) def')
      where
        -- The field that a constructor of a newtype is represented by, among its
        -- run-time fields.
        newtype : Name -> Core (Maybe Nat)
        newtype cn
            = do defs <- get Ctxt
                 Just gdef <- lookupCtxtExact cn (gamma defs)
                   | Nothing => pure Nothing
                 case definition gdef of
                      DCon _ arity (Just (_, pos)) => Just <$> newtypeField cn arity pos
                      _ => pure Nothing

        -- The newtype's field is the scrutinee, and its other run-time fields,
        -- such as `MkIORes`'s world, are erased.
        unwrap : {vars' : _} -> Maybe Nat -> List Exp.FlatVar -> Exp -> Core (CExp vars')
        unwrap k [] sc = forgetExp sc
        unwrap k (v :: vs) sc
            = do val <- if k == Just 0 then forgetExp scr else pure (CErased fc)
                 let k' = case k of
                               Just (S i) => Just i
                               _ => Nothing
                 pure (CLet fc v.name NotInline val !(unwrap {vars' = v.name :: vars'} k' vs sc))

        conAlt : Exp.FlatAlt -> Core (CConAlt vars)
        conAlt (Exp.FConAlt cn _ fvs sc)
            = do defs <- get Ctxt
                 Just gdef <- lookupCtxtExact cn (gamma defs)
                   | Nothing => undefinedName fc cn
                 let DCon tag _ _ = definition gdef
                   | _ =>
                     throw
                       (InternalError ("Flat form with a constructor that is not one: " ++ show cn))
                 let args = map name fvs
                 pure
                   (MkConAlt cn !(conInfo cn) (Just tag) args !(forgetExp {vars = args ++ vars} sc))
        conAlt (Exp.FConstAlt {}) = throw (InternalError "Flat form with mixed alternatives")

        constAlt : Exp.FlatAlt -> Core (CConstAlt vars)
        constAlt (Exp.FConstAlt k sc) = pure (MkConstAlt k !(forgetExp sc))
        constAlt (Exp.FConAlt {}) = throw (InternalError "Flat form with mixed alternatives")
    forgetExp (Exp.FCrash fc msg) = pure (CCrash fc msg)
    forgetExp (Exp.FNone fc) = pure (CErased fc)

||| Compile each function that has one of the flat forms from that form,
||| made ordinary again: the flat oracle. A copy at static arguments, which
||| has no function of its own, becomes a definition of the context that has
||| only its compiled form. Done before code generation narrows the context
||| to the compiled forms, since `forget` reads constructors and types.
export
useFlatForms : {auto c : Ref Ctxt Defs} -> NameMap Exp.FlatDef -> Core ()
useFlatForms forms = traverse_ use (toList forms)
  where
    -- The definitions a flat form refers to at run time.
    references : Exp -> List Name
    references e = toList (go e)
      where
        go : Exp -> Data.Builder Name
        go (Exp.FVar _ _) = neutral
        go (Exp.FLet _ _ v sc) = go v <+> go sc
        go (Exp.FConst _ _) = neutral
        go (Exp.FOp _ _ as) = concatMap go (toList as)
        go (Exp.FCall _ n as) = Data.Builder.single n <+> concatMap go as
        go (Exp.FPrim _ n _ _ as) = Data.Builder.single n <+> concatMap go as
        go (Exp.FStatic _ n _ _) = Data.Builder.single n
        go (Exp.FCon _ n _ _ _ as) = Data.Builder.single n <+> concatMap go as
        go (Exp.FCase _ sc alts def) = go sc <+> concatMap alt alts <+> maybe neutral go def
          where
            alt : Exp.FlatAlt -> Data.Builder Name
            alt (Exp.FConAlt n _ _ sc) = Data.Builder.single n <+> go sc
            alt (Exp.FConstAlt _ sc) = go sc
        go (Exp.FCrash _ _) = neutral
        go (Exp.FNone _) = neutral

    useForm : Name -> Exp.FlatDef -> Core ()
    useForm n d
        = do defs <- get Ctxt
             cd <- forget d
             gdef <- case !(lookupCtxtExact n (gamma defs)) of
                          Just gdef => pure gdef
                          Nothing => pure (newDef d.fc n top Scope.empty (Erased d.fc Placeholder)
                                                  (specified Public) None)
             let refs = foldr (\r => insert r False) (refersToRuntime gdef) (references d.body)
             ignore $ addDef n ({ compexpr := Just cd
                                , namedcompexpr := Just (forgetDef cd)
                                , refersToRuntimeM := Just refs } gdef)

    -- A primitive's form applies the primitive, so its body stays the
    -- function's, which the primitive's calls call.
    use : (Name, Exp.FlatDef) -> Core ()
    use (n, d@(Exp.MkFlatDef _ _ _ _ (Exp.FPrim _ p _ _ _) _)) = if p == n then pure ()
      else useForm n d
    use (n, d) = useForm n d

||| Write the flat forms to `file`, each followed by the shapes of the data
||| types it takes and returns.
export
dumpFlat : {auto c : Ref Ctxt Defs} -> String -> NameMap Exp.FlatDef -> Core ()
dumpFlat file forms
    = do texts <- traverse dumpForm (map snd (NameMap.toList forms))
         Right () <- coreLift $ Data.WriteBuilder.writeBuilder file (concat texts)
           | Left err => throw (FileErr file err)
         pure ()
  where
    isData : Exp.Skeleton -> Bool
    isData (Exp.SCon {}) = True
    isData _ = False

    -- A form, then the shape of each data type among its parameters and
    -- result.
    dumpForm : Exp.FlatDef -> Core (Data.Builder String)
    dumpForm d
        = do let sks = nub (filter isData (map skeleton d.params ++ [d.resultSkeleton]))
             shapes <- traverse (\sk => do s <- shape sk
                                           pure
                                             ("  shape " ++ show sk ++ " = " ++ maybe "none" show s
                                              ++ "\n"))
                                sks
             pure
               (Exp.defPieces d <+> Data.Builder.single "\n" <+> Data.Builder.piece shapes
                 <+> Data.Builder.single "\n")
