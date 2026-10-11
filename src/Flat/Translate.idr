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
||| A call of any other function is a call of its flat form. A function whose
||| signature is *ground*, every run-time argument and its result laid out
||| with no erased argument deciding a layout, has one, made on demand and
||| memoised: a function being translated counts as having one, so recursion
||| ends. A call at static arguments needs a form at them,
||| which is not made yet.
|||
||| A function whose result is a newtype over a function (`IO a`) takes that
||| function's arguments as its own, as `checkFlatSignature` walks it, so a
||| term of such a type is translated *applied* to the arguments its context
||| has not given it yet: the pending arguments. A static value of such a
||| type that does not reduce to its constructor, such as the call `putc c`
||| of a function, is taken apart by giving its function a name that stands
||| for the value applied to the pending arguments.
|||
||| Whatever the translation cannot place in the regime, it reports as
||| `NotFlatBody` (`Flat.Problem`), with the chain of calls from the flat
||| function it started from to it.
|||
||| The flat functions are the ones a code generator's directive names
||| (`flatNames`). The translation runs when a program is compiled, on the
||| whole context, the imported modules' case trees included, and keeps the
||| forms it makes for that compilation alone.
module Flat.Translate

import Compiler.Opts.Constructor

import Core.Case.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Flat.Exp
import Core.Normalise
import Core.Primitives
import Core.TT
import Core.Value

import Flat.Judgement

import Data.List
import Data.List1
import Data.String
import Data.Vect

import Libraries.Data.List.SizeOf
import Libraries.Data.NameMap
import Libraries.Data.WithDefault

import System.File

%default covering

||| What a name that stands for a static value stands for.
data Static : Type where
  ||| A term, with the definitions it was written inside.
  Closure : (term : ClosedTerm) -> (origin : List Name) -> Static
  ||| The function inside `value`, a value of a newtype over a function
  ||| (`IO`) that does not reduce to the newtype's constructor, with the
  ||| definitions `value` was written inside.
  Unwrapped : (value : ClosedTerm) -> (origin : List Name) -> Static

||| The translation's state: a counter for the names it makes, the
||| definitions whose forms it is making, which count as having one, the
||| static values that names stand for, the forms made, and the problem the
||| translation stopped at, which `fail` records.
record FlatState where
  constructor MkFlatState
  nextName : Int
  making : List Name
  statics : NameMap Static
  forms : NameMap FlatDef
  failure : Maybe FlatError

||| The label of the reference that holds the translation's state, a
||| `Ref FlatSt FlatState`, by which `get`, `put` and `update` find it among
||| the references in scope. It has no values: it is only ever a type.
data FlatSt : Type where

||| Where the translation is.
record Tr where
  constructor MkTr
  ||| the flat function whose form is being made
  root : Name
  ||| the callees from the root to the definition being translated
  chain : List Name
  ||| the location in the root's own code that the translation left it from
  site : FC
  ||| the definitions the term being translated was written inside
  unfolding : List Name
  ||| the flat variables in scope, with their types
  vars : NameMap (FlatVar, ClosedTerm)

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
inRoot tr = null tr.chain && all (\n => n == tr.root || blockName n) tr.unfolding

-- Stop the translation at the problem, which is recorded in the state for
-- `flatForms` to report. It is at the term's location if the root's own code
-- has it, or else where the translation left the root's code.
fail : {auto s : Ref FlatSt FlatState} -> Tr -> FC -> FlatProblem -> Core a
fail tr fc p
    = do update FlatSt { failure := Just (NotFlatBody (if inRoot tr then nonEmpty fc else tr.site)
                                                       tr.root tr.chain p) }
         throw (InternalError "the flat translation stopped")
  where
    nonEmpty : FC -> FC
    nonEmpty EmptyFC = tr.site
    nonEmpty fc = fc

-- Mark `fc` as where the translation leaves the root's code, if it does.
leave : Tr -> FC -> Tr
leave tr EmptyFC = tr
leave tr fc = if inRoot tr then { site := fc } tr else tr

inside : List Name -> Tr -> Tr
inside ns tr = { unfolding := ns } tr

addVar : FlatVar -> ClosedTerm -> Tr -> Tr
addVar fv ty tr = { vars $= insert fv.name (fv, ty) } tr

fresh : {auto s : Ref FlatSt FlatState} -> Name -> Core Name
fresh x
    = do st <- get FlatSt
         put FlatSt ({ nextName $= (+ 1) } st)
         pure (MN (nameRoot x) st.nextName)

-- `k` arguments from the front, and what follows them.
takeArgs : Nat -> List Pending -> Maybe (List ClosedTerm, List Pending)
takeArgs Z ps = Just ([], ps)
takeArgs (S k) (PArg a :: ps)
    = do (as, rest) <- takeArgs k ps
         Just (a :: as, rest)
takeArgs (S k) _ = Nothing

-- A term that names a value without computing it.
isAtom : Tr -> ClosedTerm -> Bool
isAtom tr (Ref _ Bound x) = isJust (lookup x tr.vars)
isAtom tr (Ref _ (DataCon _ Z) _) = True
isAtom tr (PrimVal {}) = True
isAtom tr (Erased {}) = True
isAtom tr _ = False

-- The term for a translated value that is an atom.
atomOf : FlatExp -> Maybe ClosedTerm
atomOf (FVar fc x) = Just (Ref fc Bound x)
atomOf (FConst fc k) = Just (PrimVal fc k)
atomOf (FNone fc) = Just (Erased fc Placeholder)
atomOf _ = Nothing

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

staticPending : {auto s : Ref FlatSt FlatState} -> Tr -> Pending -> Core Pending
staticPending tr (PArg a) = PArg <$> static tr a
staticPending tr p = pure p

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
skeleton : {auto c : Ref Ctxt Defs} -> ClosedNF -> Core Skeleton
skeleton (NPrimVal _ (PrT t)) = pure (SPrim t)
skeleton (NTCon _ n _ args) = SCon !(toFullNames n) <$> traverse argSkeleton args
  where
    argSkeleton : (FC, ClosedClosure) -> Core Skeleton
    argSkeleton (_, a) = skeleton !(evalClosure !(get Ctxt) a)
skeleton (NDCon _ n _ _ args) = SCon !(toFullNames n) <$> traverse argSkeleton args
  where
    argSkeleton : (FC, ClosedClosure) -> Core Skeleton
    argSkeleton (_, a) = skeleton !(evalClosure !(get Ctxt) a)
skeleton _ = pure SOther

||| A type's skeleton and layout, or why it is not flat.
laidOut : {auto c : Ref Ctxt Defs} -> ClosedNF -> Core (Either NotFlatReason (Skeleton, Layout))
laidOut ty
    = case !(layout [] ty) of
           LaidOut l => pure (Right (!(skeleton ty), l))
           Rejected why => pure (Left why)
           Deferred => pure (Left StuckType)

-- The tag a constructor of type `ty` carries in its layout: its tag if the
-- type has several constructors.
sumTag : {auto c : Ref Ctxt Defs} -> ClosedNF -> Int -> Core (Maybe Int)
sumTag (NTCon _ tn _ _) tag
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact tn (gamma defs)
           | Nothing => pure Nothing
         pure $ case definition gdef of
                     TCon _ _ _ _ _ (Just (_ :: _ :: _)) _ => Just tag
                     _ => Nothing
sumTag _ _ = pure Nothing

||| A binder of a function's type, at the argument given for it.
record Applied where
  constructor MkApplied
  name : Name
  rig : RigCount
  autoImplicit : Bool
  ||| its position among the explicit arguments, from 1, and its name
  position : Maybe (Nat, Name)
  type : ClosedNF

-- Whether a binder's argument exists at run time.
runtime : (Applied, a) -> Bool
runtime (b, _) = not (isErased b.rig)

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

signature : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
            ClosedTerm -> Core Signature
signature ty
    = do defs <- get Ctxt
         walk [] 0 [] !(nf defs Env.empty ty)
  where
    walk : (unfolded : List Name) -> Nat -> List SigPart -> ClosedNF -> Core Signature
    walk ns i acc (NBind fc x (Pi _ rig pinfo aty) sc)
        = do defs <- get Ctxt
             v <- fresh x
             let i' = if isExplicit pinfo then S i else i
             let b = MkApplied x rig (isAutoImplicit pinfo) (Just (i', x)) !(evalClosure defs aty)
             walk ns i' (SigArg b v :: acc)
                  !(sc defs (toClosure defaultOpts Env.empty (Ref fc Bound v)))
    walk ns i acc res
        = do Just (n, fnTy) <- newtypeOverFunction res
               | Nothing => pure (MkSignature (reverse acc) res)
             if n `elem` ns
                then pure (MkSignature (reverse acc) res)
                else walk (n :: ns) i (SigUnwrap :: acc) fnTy

-- Whether a reason for a type not to be flat makes its values static only: a
-- function, a type, a lazy value, or something holding one, such as a
-- dictionary. An argument of such a type is always a static argument, which
-- a flat form at it takes. Any other type without a layout, such as
-- `String`, has values computed at run time, and makes the callee not flat.
staticOnly : NotFlatReason -> Bool
staticOnly FunctionType = True
staticOnly RuntimeType = True
staticOnly LazyType = True
staticOnly (InField _ _ _ why) = staticOnly why
staticOnly _ = False

||| The flat variables of a ground signature's run-time arguments, with their
||| types, and its result's skeleton and layout; or why `fn`, of this
||| signature, has no flat form that a call can use.
groundSignature : {auto c : Ref Ctxt Defs} ->
                  Name -> Signature ->
                  Core (Either FlatProblem (List (FlatVar, ClosedTerm), (Skeleton, Layout)))
groundSignature fn sig
    = do let deferred = mapMaybe erasedVar sig.parts
         Right ps <- params deferred [] sig.parts
           | Left p => pure (Left p)
         case !(layout deferred sig.result) of
              LaidOut l => pure (Right (ps, (!(skeleton sig.result), l)))
              Deferred => pure (Left (NeedsCopy fn))
              Rejected why =>
                if staticOnly why
                   then pure (Left (NeedsCopy fn))
                   else pure (Left (CalleeNotFlat fn Nothing !(quoteClosed sig.result) why))
  where
    erasedVar : SigPart -> Maybe Name
    erasedVar (SigArg b v) = if isErased b.rig then Just v else Nothing
    erasedVar _ = Nothing

    params : List Name -> List (FlatVar, ClosedTerm) -> List SigPart ->
             Core (Either FlatProblem (List (FlatVar, ClosedTerm)))
    params deferred acc [] = pure (Right (reverse acc))
    params deferred acc (SigUnwrap :: ps) = params deferred acc ps
    params deferred acc (SigArg b v :: ps)
        = if isErased b.rig then params deferred acc ps else
            case !(layout deferred b.type) of
                 LaidOut l =>
                   do fv <- pure (MkFlatVar v !(skeleton b.type) l)
                      params deferred ((fv, !(quoteClosed b.type)) :: acc) ps
                 Deferred => pure (Left (NeedsCopy fn))
                 Rejected why =>
                   if b.autoImplicit || staticOnly why
                      then pure (Left (NeedsCopy fn))
                      else pure (Left (CalleeNotFlat fn b.position !(quoteClosed b.type) why))

-- The terms for a signature's first `k` binders, which a case tree of `k`
-- arguments binds, and the rest of the signature as pending arguments.
splitParts : Nat -> List SigPart -> Maybe (List ClosedTerm, List Pending)
splitParts Z ps = Just ([], map pending ps)
  where
    pending : SigPart -> Pending
    pending (SigArg _ v) = PArg (Ref EmptyFC Bound v)
    pending SigUnwrap = PUnwrap
splitParts (S k) (SigArg _ v :: ps)
    = do (ts, rest) <- splitParts k ps
         Just (Ref EmptyFC Bound v :: ts, rest)
splitParts (S k) _ = Nothing

-- The arguments of a call as static values, those of erased binders as they
-- are, so that types keep them.
staticArgs : {auto s : Ref FlatSt FlatState} ->
             Tr -> List (Applied, ClosedTerm) -> Core (List ClosedTerm)
staticArgs tr = traverse arg
  where
    arg : (Applied, ClosedTerm) -> Core ClosedTerm
    arg (b, a) = if isErased b.rig then pure a else static tr a

-- The definitions the compiler's inliner unfolds although they are not
-- marked inline.
unfoldedAnyway : List Name
unfoldedAnyway
    = [ NS primIONS (UN (Basic "io_bind"))
      , NS primIONS (UN (Basic "prim__io_bind"))
      , NS builtinNS (UN (Basic "idris_crash"))
      ]

unfoldable : Tr -> Name -> GlobalDef -> Bool
unfoldable tr fn gdef
    = let fl = gdef.flags in
          ((elem Inline fl && not (elem NoInline fl))
             || blockName fn || elem fn unfoldedAnyway)
          && not (elem fn tr.unfolding)

-- A private primitive is used only where its own module wrote it: the
-- definition the reference was written inside, the innermost being
-- unfolded or translated, is in the primitive's own source file.
checkPrivate : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
               Tr -> FC -> Name -> GlobalDef -> Core ()
checkPrivate tr fc fn gdef
    = when (collapseDefault (visibility gdef) == Private) $
        do defs <- get Ctxt
           Just writer <- pure (head' tr.unfolding)
             | Nothing => fail tr fc (PrivateElsewhere fn)
           Just wdef <- lookupCtxtExact writer (gamma defs)
             | Nothing => fail tr fc (PrivateElsewhere fn)
           case (origin (location wdef), origin (location gdef)) of
                (Just here, Just home) => unless (here == home) $ fail tr fc (PrivateElsewhere fn)
                _ => fail tr fc (PrivateElsewhere fn)
  where
    origin : FC -> Maybe OriginDesc
    origin (MkFC o _ _) = Just o
    origin (MkVirtualFC o _ _) = Just o
    origin EmptyFC = Nothing

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
conCase : List (CaseAlt vars) -> Maybe (Name, (args : List Name ** CaseTree (Scope.addInner vars args)))
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
  ||| Translate a closed term applied to `ps`, whose value has a flat type.
  trTerm : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           Tr -> ClosedTerm -> List Pending -> Core FlatExp
  trTerm tr tm ps
      = let (h, args) = getFnArgs tm in
            trApp tr h (map PArg args ++ ps)

  trApp : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
          Tr -> ClosedTerm -> List Pending -> Core FlatExp
  trApp tr (Ref fc Bound x) ps
      = case lookup x tr.vars of
             Just _ => case ps of
                            [] => pure (FVar fc x)
                            _ => fail tr fc (Unhandled "A flat value applied to arguments")
             Nothing =>
               do ps' <- traverse (staticPending tr) ps
                  case lookup x (statics !(get FlatSt)) of
                       Just (Closure t origin) => trTerm (inside origin tr) t ps'
                       Just (Unwrapped v origin) => trTerm (inside origin tr) v (PUnwrap :: ps')
                       Nothing => fail tr fc (Unhandled "An erased value used at run time")
  trApp tr (PrimVal fc c) [] = constant tr fc c
  trApp tr (Erased fc _) _ = pure (FNone fc)
  trApp tr (Bind fc x (Lam _ rig _ ty) sc) (PArg a :: ps) = bindValue tr fc x rig ty a sc ps
  trApp tr (Bind fc x (Let _ rig v ty) sc) ps = bindValue tr fc x rig ty v sc ps
  trApp tr (Bind fc _ (Lam {}) _) _ = fail tr fc NotStatic
  trApp tr (Bind fc _ (Pi {}) _) _ = fail tr fc (ValueNotFlat (TType fc (MN "top" 0)) RuntimeType)
  trApp tr (Ref fc (DataCon tag arity) n) ps = conApp tr fc n tag arity ps
  trApp tr (Ref fc (TyCon _) _) _ = fail tr fc (ValueNotFlat (TType fc (MN "top" 0)) RuntimeType)
  trApp tr (Ref fc Func n) ps = callGlobal tr fc n ps
  trApp tr (TType fc _) _ = fail tr fc (ValueNotFlat (TType fc (MN "top" 0)) RuntimeType)
  trApp tr (TForce fc _ t) ps
      = do (TDelay _ _ _ v, origin) <- whnfStatic tr t
             | _ => fail tr fc NotStatic
           ps' <- traverse (staticPending tr) ps
           trTerm (inside origin tr) v ps'
  trApp tr (TDelay fc _ _ _) _ = fail tr fc NotStatic
  trApp tr (Meta fc n _ margs) ps
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => undefinedName fc n
           let PMDef _ targs ct _ _ = definition gdef
             | _ => fail tr fc (Unhandled "An unsolved hole")
           fn <- toFullNames n
           unfold tr fc fn gdef ct (map PArg margs ++ ps)
  trApp tr tm _ = fail tr (getLoc tm) (Unhandled "This term")

  constant : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
             Tr -> FC -> Constant -> Core FlatExp
  constant tr fc (Str _)
      = fail tr fc (ValueNotFlat (PrimVal fc (PrT StringType)) (BoxedPrimitive StringType))
  constant tr fc (BI _)
      = fail tr fc (ValueNotFlat (PrimVal fc (PrT IntegerType)) (BoxedPrimitive IntegerType))
  constant tr fc (PrT _) = fail tr fc (ValueNotFlat (TType fc (MN "top" 0)) RuntimeType)
  constant tr fc WorldVal = pure (FNone fc)
  constant tr fc c = pure (FConst fc c)

  -- `let x = v in sc`, or `(\x => sc) v`, in one body: a flat value is bound
  -- to a variable unless it is an atom, and a static one is substituted.
  bindValue : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
              Tr -> FC -> (x : Name) -> RigCount -> (ty : ClosedTerm) ->
              (v : ClosedTerm) -> Term [x] -> List Pending -> Core FlatExp
  bindValue tr fc x rig ty v sc ps
      = if isErased rig || isAtom tr v then trTerm tr (subst v sc) ps else
          do defs <- get Ctxt
             ty' <- resolved ty
             Right (sk, l) <- laidOut !(nf defs Env.empty ty')
               | Left _ => trTerm tr (subst v sc) ps
             v' <- trTerm tr v []
             let Nothing = atomOf v'
               | Just a => trTerm tr (subst a sc) ps
             x' <- fresh x
             let fv = MkFlatVar x' sk l
             body <- trTerm (addVar fv ty' tr) (subst (Ref fc Bound x') sc) ps
             pure (FLet fc fv v' body)

  -- A constructor applied to `ps`: a flat value, or a newtype's function
  -- when the context unwraps it.
  conApp : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           Tr -> FC -> Name -> (tag : Int) -> (arity : Nat) -> List Pending -> Core FlatExp
  conApp tr fc n tag arity ps
      = do Just (cargs, rest) <- pure (takeArgs arity ps)
             | Nothing => fail tr fc NotStatic
           defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => undefinedName fc n
           Just (bs, resTy) <- applyType (type gdef) cargs
             | Nothing => fail tr fc (Unhandled "A constructor of another arity")
           let fields = map snd (filter runtime (zip bs cargs))
           case rest of
                [] => do Right (sk, l) <- laidOut resTy
                           | Left why => fail tr fc (ValueNotFlat !(quoteClosed resTy) why)
                         fs <- traverse (\f => trTerm tr f []) fields
                         pure (FCon fc !(toFullNames n) !(sumTag resTy tag) sk l fs)
                PUnwrap :: rest' =>
                  case fields of
                       [f] => trTerm tr f rest'
                       _ => fail tr fc (Unhandled "A newtype without one field")
                _ => fail tr fc (Unhandled "A constructor applied to too many arguments")

  callGlobal : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
               Tr -> FC -> Name -> List Pending -> Core FlatExp
  callGlobal tr fc n ps
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => undefinedName fc n
           fn <- toFullNames n
           case definition gdef of
                Builtin op => primOp tr fc fn gdef op ps
                ExternDef ar => primitive tr fc fn gdef ar ps
                ForeignDef ar _ => primitive tr fc fn gdef ar ps
                PMDef _ targs ct _ _ =>
                  if unfoldable tr fn gdef
                     then unfold tr fc fn gdef ct ps
                     else demand tr fc fn gdef ps
                _ => fail tr fc (Unhandled ("The reference to " ++ show fn))

  -- The run-time arguments of a call of a primitive, which must be flat.
  primArgs : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
             Tr -> FC -> Name -> List (Applied, ClosedTerm) -> Core (List FlatExp)
  primArgs tr fc fn bas = traverse arg (filter runtime bas)
    where
      arg : (Applied, ClosedTerm) -> Core FlatExp
      arg (b, a)
          = do Right _ <- laidOut b.type
                 | Left why => fail tr fc (CalleeNotFlat fn b.position !(quoteClosed b.type) why)
               trTerm tr a []

  primOp : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           {arity : Nat} ->
           Tr -> FC -> Name -> GlobalDef -> PrimFn arity -> List Pending -> Core FlatExp
  primOp tr fc fn gdef op ps
      = do Just (args, rest) <- pure (takeArgs arity ps)
             | Nothing => fail tr fc NotStatic
           case op of
                Crash => crash args
                BelieveMe => believe args rest
                _ => do Nothing <- foldOp tr fc op args
                          | Just c => trTerm tr c rest
                        Just (bs, resTy) <- applyType (type gdef) args
                          | Nothing => fail tr fc (Unhandled "A primitive of another arity")
                        Right _ <- laidOut resTy
                          | Left why => fail tr fc (CalleeNotFlat fn Nothing !(quoteClosed resTy) why)
                        as <- primArgs tr fc fn (zip bs args)
                        let Just vs = toVect arity as
                          | Nothing => fail tr fc (Unhandled "A primitive of another arity")
                        case rest of
                             [] => pure (FOp fc op vs)
                             _ => fail tr fc (Unhandled "A primitive applied to too many arguments")
    where
      crash : List ClosedTerm -> Core FlatExp
      crash [_, msg]
          = do (PrimVal _ (Str str), _) <- whnfStatic tr msg
                 | _ => fail tr fc (ValueNotFlat (PrimVal fc (PrT StringType))
                                                 (BoxedPrimitive StringType))
               pure (FCrash fc str)
      crash _ = fail tr fc (Unhandled "A crash of another arity")

      -- Between types of one layout, a value is its own coercion.
      believe : List ClosedTerm -> List Pending -> Core FlatExp
      believe [a, b, x] rest
          = do defs <- get Ctxt
               a' <- resolved a
               b' <- resolved b
               Right (_, la) <- laidOut !(nf defs Env.empty a')
                 | Left why => fail tr fc (ValueNotFlat a' why)
               Right (_, lb) <- laidOut !(nf defs Env.empty b')
                 | Left why => fail tr fc (ValueNotFlat b' why)
               if la == lb
                  then trTerm tr x rest
                  else fail tr fc (Unhandled "A coercion between layouts")
      believe _ _ = fail tr fc (Unhandled "A coercion of another arity")

  -- An `%extern` or `%foreign` primitive.
  primitive : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
              Tr -> FC -> Name -> GlobalDef -> (arity : Nat) -> List Pending -> Core FlatExp
  primitive tr fc fn gdef arity ps
      = do Just (args, rest) <- pure (takeArgs arity ps)
             | Nothing => fail tr fc NotStatic
           checkPrivate tr fc fn gdef
           Just (bs, resTy) <- applyType (type gdef) args
             | Nothing => fail tr fc (Unhandled "A primitive of another arity")
           Right _ <- laidOut resTy
             | Left why => fail tr fc (CalleeNotFlat fn Nothing !(quoteClosed resTy) why)
           as <- primArgs tr fc fn (zip bs args)
           case rest of
                [] => pure (FPrim fc fn as)
                _ => fail tr fc (Unhandled "A primitive applied to too many arguments")

  -- A call of a definition that is unfolded: its case tree, at the call's
  -- arguments. Each flat one is bound to a variable unless it is an atom, so
  -- that it is computed once and in order, and each static one, like what
  -- the call is applied to, is passed as a closure.
  unfold : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           {targs : _} ->
           Tr -> FC -> Name -> GlobalDef -> CaseTree targs -> List Pending -> Core FlatExp
  unfold tr fc fn gdef ct ps
      = do Just (args, rest) <- pure (takeArgs (length targs) ps)
             | Nothing => fail tr fc NotStatic
           Just (bs, _) <- applyType (type gdef) args
             | Nothing => fail tr fc (Unhandled "A definition of another arity")
           (args', wrap, tr') <- bindArgs tr fc (zip bs args)
           rest' <- traverse (staticPending tr') rest
           let tr'' = { unfolding $= (fn ::) } (if blockName fn then tr' else leave tr' fc)
           let Just env = mkSubst targs args'
             | Nothing => fail tr fc (Unhandled "A definition of another arity")
           wrap <$> trTree tr'' env ct rest'

  bindArgs : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
             Tr -> FC -> List (Applied, ClosedTerm) ->
             Core (List ClosedTerm, FlatExp -> FlatExp, Tr)
  bindArgs tr fc [] = pure ([], id, tr)
  bindArgs tr fc ((b, a) :: bas)
      = if isErased b.rig || isAtom tr a then keep a else
          do Right (sk, l) <- laidOut b.type
               | Left _ => keep !(static tr a)
             v <- trTerm tr a []
             let Nothing = atomOf v
               | Just a' => keep a'
             x <- fresh b.name
             let fv = MkFlatVar x sk l
             (as, wrap, tr') <- bindArgs (addVar fv !(quoteClosed b.type) tr) fc bas
             pure (Ref fc Bound x :: as, FLet fc fv v . wrap, tr')
    where
      keep : ClosedTerm -> Core (List ClosedTerm, FlatExp -> FlatExp, Tr)
      keep a' = do (as, wrap, tr') <- bindArgs tr fc bas
                   pure (a' :: as, wrap, tr')

  -- A call of a function that is not unfolded: a call of its flat form.
  demand : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           Tr -> FC -> Name -> GlobalDef -> List Pending -> Core FlatExp
  demand tr fc fn gdef ps
      = do sig <- signature (type gdef)
           Right (params, res) <- groundSignature fn sig
             | Left p => fail tr fc p
           let args = mapMaybe pendingArg ps
           let erasure = mapMaybe binderErased sig.parts
           when (length args /= length erasure) $ fail tr fc NotStatic
           as <- traverse (\a => trTerm tr a []) (map fst (filter (not . snd) (zip args erasure)))
           makeForm tr fc fn gdef sig params res
           pure (FCall fc fn as)
    where
      pendingArg : Pending -> Maybe ClosedTerm
      pendingArg (PArg a) = Just a
      pendingArg _ = Nothing

      binderErased : SigPart -> Maybe Bool
      binderErased (SigArg b _) = Just (isErased b.rig)
      binderErased _ = Nothing

  ||| Make the flat form of `fn`, of a ground signature, unless it has one or
  ||| is being made.
  makeForm : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
             Tr -> FC -> Name -> GlobalDef -> Signature ->
             List (FlatVar, ClosedTerm) -> (Skeleton, Layout) -> Core ()
  makeForm tr fc fn gdef sig params (rsk, rl)
      = do Nothing <- pure (lookup fn (forms !(get FlatSt)))
             | Just _ => pure ()
           st <- get FlatSt
           when (not (fn `elem` st.making)) $
             do let tr' = { chain := if fn == tr.root then [] else tr.chain ++ [fn]
                          , unfolding := [fn]
                          , vars := fromList (map (\p => ((fst p).name, p)) params)
                          } (if fn == tr.root then tr else leave tr fc)
                let PMDef _ targs ct _ _ = definition gdef
                  | _ => fail tr' fc (Unhandled "A definition without clauses")
                put FlatSt ({ making $= (fn ::) } st)
                let Just (envTms, pending) = splitParts (length targs) sig.parts
                  | Nothing => fail tr' fc (Unhandled "Clauses with more arguments than the type")
                let Just env = mkSubst targs envTms
                  | Nothing => fail tr' fc (Unhandled "Clauses with more arguments than the type")
                body <- trTree tr' env ct pending
                let d = MkFlatDef fn (map fst params) rsk rl body (location gdef)
                update FlatSt { forms $= insert fn d }

  ||| Translate a case tree, its variables bound to `env`, applied to `ps`.
  trTree : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           {vars : _} ->
           Tr -> SubstEnv vars Scope.empty -> CaseTree vars -> List Pending -> Core FlatExp
  trTree tr env (STerm _ t) ps = trTerm tr (instantiate env t) ps
  trTree tr env (Unmatched msg) ps = pure (FCrash tr.site msg)
  trTree tr env Impossible ps = pure (FCrash tr.site "Impossible case")
  trTree tr env (Case idx p scTy alts) ps
      = case Var.index env (MkVar p) of
             Ref fc Bound x =>
               case lookup x tr.vars of
                    Just (_, ty) => flatCase tr env fc x ty alts ps
                    Nothing =>
                      case lookup x (statics !(get FlatSt)) of
                           Just _ => staticCase tr env (Ref fc Bound x) scTy alts ps
                           Nothing => erasedCase tr env fc alts ps
             Erased fc _ => erasedCase tr env fc alts ps
             scr => staticCase tr env scr scTy alts ps

  -- A case on a flat variable: a case at run time.
  flatCase : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
             {vars : _} ->
             Tr -> SubstEnv vars Scope.empty -> FC -> Name -> ClosedTerm ->
             List (CaseAlt vars) -> List Pending -> Core FlatExp
  flatCase tr env fc x ty alts ps
      = do defs <- get Ctxt
           tyNF <- nf defs Env.empty ty
           (cas, def) <- go tyNF alts
           pure (FCase fc (FVar fc x) cas def)
    where
      go : ClosedNF -> List (CaseAlt vars) -> Core (List FlatAlt, Maybe FlatExp)
      go tyNF [] = pure ([], Nothing)
      go tyNF (ConCase cn tag args sc :: as)
          = do (vals, fvs, tr') <- openCon tr fc tyNF cn args Nothing
               let Just env' = extendSubst args vals env
                 | Nothing => fail tr fc (Unhandled "A constructor pattern of another arity")
               body <- trTree tr' env' sc ps
               (rest, def) <- go tyNF as
               pure (FConAlt !(toFullNames cn) !(sumTag tyNF tag) fvs body :: rest, def)
      go tyNF (ConstCase k sc :: as)
          = do body <- trTree tr env sc ps
               (rest, def) <- go tyNF as
               pure (FConstAlt k body :: rest, def)
      go tyNF (DefaultCase sc :: _)
          = do body <- trTree tr env sc ps
               pure ([], Just body)
      go tyNF (DelayCase {} :: _) = fail tr fc (ValueNotFlat ty LazyType)

  -- The values of a constructor pattern's variables, at a scrutinee of type
  -- `tyNF`: a fresh flat variable for each run-time field, the type's
  -- argument for an erased binder the type's arguments give, and a fresh
  -- name for any other erased binder, which is never used at run time. For
  -- a static scrutinee of a newtype over a function, given with where it
  -- was written, the field is a name for it unwrapped instead.
  openCon : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
            Tr -> FC -> ClosedNF -> Name -> List Name ->
            (unwrapping : Maybe (ClosedTerm, List Name)) ->
            Core (List ClosedTerm, List FlatVar, Tr)
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
             List ClosedTerm -> List FlatVar -> Tr ->
             Core (List ClosedTerm, List FlatVar, Tr)
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
                                   sc' <- sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound v))
                                   bind ps tyArgs (S i) as sc' (Ref bfc Bound v :: vals) fvs tr
                          Right (sk, l) <- laidOut atyNF
                            | Left why => fail tr fc (ValueNotFlat !(quoteClosed atyNF) why)
                          let fv = MkFlatVar v sk l
                          sc' <- sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound v))
                          bind ps tyArgs (S i) as sc' (Ref bfc Bound v :: vals) (fv :: fvs)
                               (addVar fv !(quoteClosed atyNF) tr)
      bind ps tyArgs i [] _ vals fvs tr = pure (reverse vals, reverse fvs, tr)
      bind _ _ _ _ _ _ _ _ = fail tr fc (Unhandled "A constructor pattern of another arity")

  -- A case on an erased value, which the run-time tree does not have: the
  -- case has one alternative.
  erasedCase : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
               {vars : _} ->
               Tr -> SubstEnv vars Scope.empty -> FC -> List (CaseAlt vars) ->
               List Pending -> Core FlatExp
  erasedCase tr env fc [ConCase _ _ args sc] ps
      = do vals <- traverse (\a => Ref fc Bound <$> fresh a) args
           let Just env' = extendSubst args vals env
             | Nothing => fail tr fc (Unhandled "A constructor pattern of another arity")
           trTree tr env' sc ps
  erasedCase tr env fc [DefaultCase sc] ps = trTree tr env sc ps
  erasedCase tr env fc _ ps = fail tr fc (Unhandled "A case on an erased value")

  -- A case on a static value: the alternative it selects. A value of a
  -- newtype over a function that does not reduce selects the newtype's
  -- constructor, its function unwrapped.
  staticCase : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
               {vars : _} ->
               Tr -> SubstEnv vars Scope.empty -> ClosedTerm -> Term vars ->
               List (CaseAlt vars) -> List Pending -> Core FlatExp
  staticCase tr env scr scTy alts ps
      = do (v, origin) <- whnfStatic tr scr
           case getFnArgs v of
                (Ref _ (DataCon {}) cn, cargs) =>
                  do cn' <- toFullNames cn
                     conAlt cn' !(conArgs (inside origin tr) cn' cargs) alts
                (PrimVal _ k, []) => constAlt k alts
                _ => do tyNF <- stuckType env v scTy
                        Just _ <- newtypeOverFunction tyNF
                          | Nothing => do Right _ <- laidOut tyNF
                                            | Left why => fail tr (getLoc scr) (ValueNotFlat !(quoteClosed tyNF) why)
                                          fail tr (getLoc scr) (Unhandled "A case on a value that is not a variable")
                        Just (cn, (args ** sc)) <- pure (conCase alts)
                          | Nothing => fail tr (getLoc scr) NotStatic
                        (vals, _, tr') <- openCon tr (getLoc scr) tyNF cn args (Just (v, origin))
                        let Just env' = extendSubst args vals env
                          | Nothing => fail tr (getLoc scr) (Unhandled "A constructor pattern of another arity")
                        trTree tr' env' sc ps
    where
      conAlt : Name -> List ClosedTerm -> List (CaseAlt vars) -> Core FlatExp
      conAlt cn cargs [] = pure (FCrash (getLoc scr) "Unmatched case")
      conAlt cn cargs (ConCase n _ args sc :: as)
          = if !(toFullNames n) == cn
               then do let Just env' = extendSubst args cargs env
                         | Nothing => fail tr (getLoc scr) (Unhandled "A constructor pattern of another arity")
                       trTree tr env' sc ps
               else conAlt cn cargs as
      conAlt cn cargs (DefaultCase sc :: _) = trTree tr env sc ps
      conAlt cn cargs (_ :: as) = conAlt cn cargs as

      constAlt : Constant -> List (CaseAlt vars) -> Core FlatExp
      constAlt k [] = pure (FCrash (getLoc scr) "Unmatched case")
      constAlt k (ConstCase k' sc :: as)
          = if k == k' then trTree tr env sc ps else constAlt k as
      constAlt k (DefaultCase sc :: _) = trTree tr env sc ps
      constAlt k (_ :: as) = constAlt k as

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
      -- A call of `n`, unfolded if it is unfoldable or a solved hole.
      whnfCall : FC -> Name -> (hole : Bool) -> List ClosedTerm -> Core (ClosedTerm, List Name)
      whnfCall fc n hole as
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                 | Nothing => pure (tm, tr.unfolding)
               fn <- toFullNames n
               case definition gdef of
                    PMDef _ targs ct _ _ =>
                      if (hole || unfoldable tr fn gdef) && length as >= length targs
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

  -- A case tree on static values, if it selects a leaf, with the definitions
  -- the leaf was written inside.
  evalStatic : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
               {vars : _} ->
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
                        Just _ <- newtypeOverFunction tyNF
                          | Nothing => pure Nothing
                        Just (cn, (args ** sc)) <- pure (conCase alts)
                          | Nothing => pure Nothing
                        (vals, _, _) <- openCon tr (getLoc v) tyNF cn args (Just (v, origin))
                        let Just env' = extendSubst args vals env
                          | Nothing => pure Nothing
                        evalStatic tr env' sc
    where
      conAlt : Name -> List ClosedTerm -> List (CaseAlt vars) -> Core (Maybe (ClosedTerm, List Name))
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

  -- A primitive operation on constants, done now.
  foldOp : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
           {arity : Nat} ->
           Tr -> FC -> PrimFn arity -> List ClosedTerm -> Core (Maybe ClosedTerm)
  foldOp tr fc op as
      = do as' <- traverse (\a => fst <$> whnfStatic tr a) as
           let Just ks = the (Maybe (List Constant)) (traverse constantOf as')
             | Nothing => pure Nothing
           let Just vs = toVect arity (map (NPrimVal fc) ks)
             | Nothing => pure Nothing
           case getOp {vars = Scope.empty} op vs of
                Just (NPrimVal _ k) => pure (Just (PrimVal fc k))
                _ => pure Nothing
    where
      constantOf : ClosedTerm -> Maybe Constant
      constantOf (PrimVal _ k) = Just k
      constantOf _ = Nothing

-- Make the flat form of `n`, a flat function, if its signature is ground.
-- A generic one has flat forms at static arguments only.
root : {auto c : Ref Ctxt Defs} -> {auto s : Ref FlatSt FlatState} ->
       Name -> Core ()
root n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
           | Nothing => pure ()
         fn <- toFullNames n
         sig <- signature (type gdef)
         Right (params, res) <- groundSignature fn sig
           | Left _ => pure ()
         let tr = MkTr fn [] (location gdef) [] empty
         makeForm tr (location gdef) fn gdef sig params res

||| The flat functions a code generator's directives name: each directive
||| `flat` followed by names, each as written in the program, qualified as
||| far as it takes to name one function. A name that names none, or more
||| than one, is an error.
export
flatNames : {auto c : Ref Ctxt Defs} -> (directives : List String) -> Core (List Name, List FlatError)
flatNames directives
    = do -- Idris gives a module's directives last first
         found <- traverse one (concatMap names (reverse directives))
         pure (mapMaybe ok found, mapMaybe bad found)
  where
    names : String -> List String
    names d = case words d of
                   ("flat" :: ns) => ns
                   _ => []

    parsed : String -> Name
    parsed str = case reverse (forget (split (== '.') str)) of
                      [n] => UN (Basic n)
                      (n :: ns) => NS (mkNamespace (concat (intersperse "." (reverse ns)))) (UN (Basic n))
                      [] => UN (Basic str)

    one : String -> Core (Either FlatError Name)
    one str
        = do defs <- get Ctxt
             found <- lookupCtxtName (parsed str) (gamma defs)
             case found of
                  [(n, _, _)] => Right <$> toFullNames n
                  ms => pure (Left (UnknownFlatName str !(traverse (\(n, _, _) => toFullNames n) ms)))

    ok : Either FlatError Name -> Maybe Name
    ok (Right n) = Just n
    ok _ = Nothing

    bad : Either FlatError Name -> Maybe FlatError
    bad (Left e) = Just e
    bad _ = Nothing

||| The flat forms of the flat functions given, and of the ground functions
||| they call, with the errors of those that have none: a signature that is
||| not flat, or a body. A function that fails leaves no forms behind, of its
||| own or of its callees.
export
flatForms : {auto c : Ref Ctxt Defs} -> List Name -> Core (NameMap FlatDef, List FlatError)
flatForms ns
    = do s <- newRef FlatSt (MkFlatState 0 [] empty empty Nothing)
         errs <- catMaybes <$> traverse tryRoot ns
         pure ((forms !(get FlatSt)), errs)
  where
    tryRoot : {auto s : Ref FlatSt FlatState} -> Name -> Core (Maybe FlatError)
    tryRoot n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure Nothing
             Nothing <- checkFlatSignature (location gdef) n
               | err => pure err
             before <- get FlatSt
             catch (do root n; pure Nothing)
                   (\err => do st <- get FlatSt
                               put FlatSt ({ forms := forms before, making := [], failure := Nothing } st)
                               case failure st of
                                    Just e => pure (Just e)
                                    Nothing => throw err)

-- The id ordinary code gives an intrinsic constructor, as
-- `Compiler.Opts.Constructor` names and numbers them.
intrinsicTag : ConInfo -> Maybe Int
intrinsicTag NIL = Just 0
intrinsicTag CONS = Just 1
intrinsicTag NOTHING = Just 0
intrinsicTag JUST = Just 1
intrinsicTag _ = Nothing

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

atIndex : Nat -> List a -> Maybe a
atIndex _ [] = Nothing
atIndex Z (x :: _) = Just x
atIndex (S k) (_ :: xs) = atIndex k xs

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
shape : {auto c : Ref Ctxt Defs} -> Skeleton -> Core (Maybe Shape)
shape sk
    = do Just tm <- skeletonTerm sk
           | Nothing => pure Nothing
         defs <- get Ctxt
         shapeOf !(nf defs Env.empty tm)
  where
    skeletonTerm : Skeleton -> Core (Maybe ClosedTerm)
    skeletonTerm (SPrim t) = pure (Just (PrimVal EmptyFC (PrT t)))
    skeletonTerm (SCon n as)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure Nothing
             Just as' <- sequence <$> traverse skeletonTerm as
               | Nothing => pure Nothing
             pure $ case definition gdef of
                         TCon a _ _ _ _ _ _ => Just (apply EmptyFC (Ref EmptyFC (TyCon a) n) as')
                         DCon t a _ => Just (apply EmptyFC (Ref EmptyFC (DataCon t a) n) as')
                         _ => Nothing
    skeletonTerm SOther = pure (Just (Erased EmptyFC Placeholder))

    -- The judgement goes first: it rejects the recursive types, whose
    -- shapes have no end.
    mutual
      shapeOf : ClosedNF -> Core (Maybe Shape)
      shapeOf ty@(NPrimVal _ (PrT t))
          = do LaidOut _ <- layout [] ty
                 | _ => pure Nothing
               pure (Just (PrimShape t))
      shapeOf ty@(NTCon _ n _ args)
          = do LaidOut _ <- layout [] ty
                 | _ => pure Nothing
               defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                 | Nothing => pure Nothing
               let TCon _ _ _ _ _ (Just cons) _ = definition gdef
                 | _ => pure Nothing
               cs <- traverse (conShape args) cons
               pure (DataShape <$> the (Maybe (List ConShape)) (sequence cs))
      shapeOf _ = pure Nothing

      conShape : List (FC, ClosedClosure) -> Name -> Core (Maybe ConShape)
      conShape args cn
          = do defs <- get Ctxt
               Just cdef <- lookupCtxtExact cn (gamma defs)
                 | Nothing => pure Nothing
               let DCon tag arity nt = definition cdef
                 | _ => pure Nothing
               fs <- traverse (\t => shapeOf !(nf defs Env.empty t)) !(fieldTypes args cdef)
               let Just fs' = the (Maybe (List Shape)) (sequence fs)
                 | Nothing => pure Nothing
               ord <- case nt of
                           Just (_, pos) => AsField <$> newtypeField cn arity pos
                           Nothing => pure (ordinary tag !(conInfo cn))
               pure (Just (MkConShape !(toFullNames cn) tag ord fs'))

      -- As `Compiler.Opts.Constructor` represents a constructor that is not
      -- a newtype's.
      ordinary : Int -> ConInfo -> Ordinary
      ordinary tag (ENUM _) = AsTag
      ordinary tag ci = AsObject (fromMaybe tag (intrinsicTag ci))

mutual
  forgetExp : {auto c : Ref Ctxt Defs} -> {vars : _} -> FlatExp -> Core (CExp vars)
  forgetExp (FVar fc x)
      = case isVar x vars of
             Just (MkVar p) => pure (CLocal fc p)
             Nothing => throw (InternalError ("Flat form with an unbound variable " ++ show x))
  forgetExp (FLet fc v val sc)
      = pure (CLet fc v.name NotInline !(forgetExp val) !(forgetExp {vars = v.name :: vars} sc))
  forgetExp (FConst fc k) = pure (CPrimVal fc k)
  forgetExp (FOp fc op as) = COp fc op <$> forgetArgs as
  forgetExp (FCall fc n as) = CApp fc (CRef fc n) <$> traverse forgetExp as
  forgetExp (FPrim fc n as)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => undefinedName fc n
           let arity = case definition gdef of
                            ExternDef a => a
                            ForeignDef a _ => a
                            _ => length as
           CApp fc (CRef fc n) <$> withErased fc !(erasure n arity) !(traverse forgetExp as)
  forgetExp (FCon fc cn _ _ _ as)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact cn (gamma defs)
             | Nothing => undefinedName fc cn
           as' <- traverse forgetExp as
           case definition gdef of
                DCon _ arity (Just (_, pos)) =>
                  do Just a <- pure (atIndex !(newtypeField cn arity pos) as')
                       | Nothing => throw (InternalError ("Flat form with a newtype of no field: " ++ show cn))
                     pure a
                DCon tag _ _ => pure (CCon fc cn !(conInfo cn) (Just tag) as')
                _ => throw (InternalError ("Flat form with a constructor that is not one: " ++ show cn))
  forgetExp (FCase fc scr alts def)
      = do scr' <- forgetExp scr
           def' <- traverseOpt forgetExp def
           case alts of
                [] => pure (fromMaybe (CCrash fc "No alternative") def')
                (FConstAlt {} :: _) => pure (CConstCase fc scr' !(traverse constAlt alts) def')
                [FConAlt cn _ fvs sc] =>
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
      unwrap : {vars' : _} -> Maybe Nat -> List FlatVar -> FlatExp -> Core (CExp vars')
      unwrap k [] sc = forgetExp sc
      unwrap k (v :: vs) sc
          = do val <- if k == Just 0 then forgetExp scr else pure (CErased fc)
               let k' = case k of
                             Just (S i) => Just i
                             _ => Nothing
               pure (CLet fc v.name NotInline val !(unwrap {vars' = v.name :: vars'} k' vs sc))

      conAlt : FlatAlt -> Core (CConAlt vars)
      conAlt (FConAlt cn _ fvs sc)
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact cn (gamma defs)
                 | Nothing => undefinedName fc cn
               let DCon tag _ _ = definition gdef
                 | _ => throw (InternalError ("Flat form with a constructor that is not one: " ++ show cn))
               let args = map name fvs
               pure (MkConAlt cn !(conInfo cn) (Just tag) args !(forgetExp {vars = args ++ vars} sc))
      conAlt (FConstAlt {}) = throw (InternalError "Flat form with mixed alternatives")

      constAlt : FlatAlt -> Core (CConstAlt vars)
      constAlt (FConstAlt k sc) = pure (MkConstAlt k !(forgetExp sc))
      constAlt (FConAlt {}) = throw (InternalError "Flat form with mixed alternatives")
  forgetExp (FCrash fc msg) = pure (CCrash fc msg)
  forgetExp (FNone fc) = pure (CErased fc)

  forgetArgs : {auto c : Ref Ctxt Defs} -> {vars : _} -> Vect n FlatExp -> Core (Vect n (CExp vars))
  forgetArgs [] = pure []
  forgetArgs (a :: as) = pure (!(forgetExp a) :: !(forgetArgs as))

  -- The arguments of a primitive's call, the erased ones as `CErased`.
  withErased : FC -> List Bool -> List (CExp vars) -> Core (List (CExp vars))
  withErased fc (True :: es) as = (CErased fc ::) <$> withErased fc es as
  withErased fc (False :: es) (a :: as) = (a ::) <$> withErased fc es as
  withErased fc _ as = pure as

||| The ordinary form of a flat form: every value represented as ordinary code
||| represents it, every call by name, taking the definition's run-time
||| arguments as ordinary code passes them. It witnesses that the flat regime
||| is part of the ordinary one, and is the flat translation's test oracle.
||| Like every compiled form, it then has its constructors specialised
||| (`Compiler.Opts.Constructor`).
export
forget : {auto c : Ref Ctxt Defs} -> FlatDef -> Core CDef
forget d
    = do let args = map name d.params
         s <- newRef NextMN 0
         constructorCDef (MkFun args !(forgetExp {vars = args} d.body))

-- The definitions a flat form refers to at run time.
references : FlatExp -> List Name
references (FVar _ _) = []
references (FLet _ _ v sc) = references v ++ references sc
references (FConst _ _) = []
references (FOp _ _ as) = concatMap references (toList as)
references (FCall _ n as) = n :: concatMap references as
references (FPrim _ n as) = n :: concatMap references as
references (FCon _ n _ _ _ as) = n :: concatMap references as
references (FCase _ sc alts def)
    = references sc ++ concatMap alt alts ++ maybe [] references def
  where
    alt : FlatAlt -> List Name
    alt (FConAlt n _ _ sc) = n :: references sc
    alt (FConstAlt _ sc) = references sc
references (FCrash _ _) = []
references (FNone _) = []

||| Compile each function that has one of the flat forms from that form,
||| made ordinary again: the flat oracle. Done before code generation narrows
||| the context to the compiled forms, since `forget` reads constructors and
||| types.
export
useFlatForms : {auto c : Ref Ctxt Defs} -> NameMap FlatDef -> Core ()
useFlatForms forms = traverse_ use (toList forms)
  where
    use : (Name, FlatDef) -> Core ()
    use (n, d)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure ()
             cd <- forget d
             let refs = foldr (\r => insert r False) (refersToRuntime gdef) (references d.body)
             ignore $ addDef n ({ compexpr := Just cd
                                , namedcompexpr := Just (forgetDef cd)
                                , refersToRuntimeM := Just refs } gdef)

||| Write the flat forms to `file`, each followed by the shapes of the data
||| types it takes and returns.
export
dumpFlat : {auto c : Ref Ctxt Defs} -> String -> NameMap FlatDef -> Core ()
dumpFlat file forms
    = do texts <- traverse dumpForm (map snd (toList forms))
         Right () <- coreLift $ writeFile file (fastConcat texts)
           | Left err => throw (FileErr file err)
         pure ()
  where
    isData : Skeleton -> Bool
    isData (SCon {}) = True
    isData _ = False

    -- A form, then the shape of each data type among its parameters and
    -- result.
    dumpForm : FlatDef -> Core String
    dumpForm d
        = do let sks = nub (filter isData (map skeleton d.params ++ [d.resultSkeleton]))
             shapes <- traverse (\sk => do s <- shape sk
                                           pure ("  shape " ++ show sk ++ " = " ++ maybe "none" show s ++ "\n"))
                                sks
             pure (show d ++ "\n" ++ fastConcat shapes ++ "\n")
