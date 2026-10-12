||| Flat functions: the types whose values need no heap, their layouts, and
||| the check of a flat function's signature.
|||
||| A type is *flat* if it is one of:
|||
||| - a machine integer, `Char`, `Double` or `%World`;
||| - a type that is not recursive and whose constructors' run-time fields
|||   are all flat: records, newtypes, tokens (one constructor, no run-time
|||   fields), enumerations (no constructor with run-time fields), and sums
|||   such as `Maybe Bits64`;
||| - a type with no constructors that is not external, which has no values.
|||
||| A type is recursive when its declaration is: when the run-time fields of
||| its constructors, at its own parameters, reach it again through the
||| declarations of the type constructors they mention. So `List` is
||| recursive, and `Pair` is not, although `(Bits64, Bits64, Bits64)` nests
||| one `Pair` in another.
|||
||| Erased arguments, fields and indices take no part, and a type's arguments
||| are judged where it is applied: `Pair Bits64 Bool` is flat,
||| `Pair String Bool` is not. The judgement looks through `export`-only
||| abstraction, as the newtype optimisation does.
|||
||| A flat type has a layout (`Flat.Exp`): the registers its values
||| take. A machine integer and a `Char` take a `Word`, a `Double` a `Dbl`; a
||| token, `%World` and anything erased take none; a type with one
||| constructor takes its run-time fields' layouts in turn, and a type with
||| several takes a `Word` for the tag first, then each constructor's fields'
||| layouts in turn, sharing no register between constructors.
module Flat.Judgement

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.Env
import public Flat.Exp
import public Flat.Problem
import Core.Normalise
import Core.TT
import Core.Value

import Libraries.Data.NameMap

%default covering

||| What a judgement depends on.
record Judging where
  constructor MkJudging
  ||| The function's erased arguments. A type made of them is known only in a
  ||| specialisation of the function, where it is judged in turn.
  deferred : List Name

mentions : List Name -> ClosedTerm -> Bool
mentions ns tm
    = let refs = getRefs (UN Underscore) tm in
          any (\n => isJust (lookup n refs)) ns

argAt : Nat -> List a -> Maybe a
argAt _ [] = Nothing
argAt Z (x :: _) = Just x
argAt (S k) (_ :: xs) = argAt k xs

-- A name for the i-th binder of a constructor's type.
binderName : Nat -> Name
binderName i = MN "flat" (cast i)

||| The run-time fields of a constructor at a type's arguments `args`, each
||| with its name and type, and the constructor's erased binders that `args`
||| do not determine.
|||
||| A constructor's type, `{0 a, b : Type} -> (fst : a) -> (snd : b) -> Pair a
||| b`, names the type's arguments in its result. A first walk finds which
||| binder the result gives as which argument; a second substitutes `args`
||| for those binders and collects the fields. Any other binder stays a name
||| of its own: a field's value, or an index the constructor fixes, as in
||| `MkSome : {0 n : Nat} -> Vect n a -> Some a`. The erased ones among them
||| are the undetermined.
conFields : {auto c : Ref Ctxt Defs} ->
            (args : List (FC, ClosedClosure)) -> (conTy : ClosedNF) ->
            Core (List (Name, ClosedNF), List Name)
conFields args conTy
    = do positions <- resultPositions 0 conTy
         fields positions [] [] 0 conTy
  where
    own : FC -> Nat -> ClosedClosure
    own fc i = toClosure defaultOpts Env.empty (Ref fc Bound (binderName i))

    given : ClosedNF -> Maybe Nat
    given (NApp _ (NRef Bound (MN "flat" b)) []) = Just (cast b)
    given _ = Nothing

    -- (binder, argument position) for each binder the result gives as an
    -- argument of the type
    resultPositions : Nat -> ClosedNF -> Core (List (Nat, Nat))
    resultPositions i (NBind fc _ (Pi {}) sc)
        = do defs <- get Ctxt
             resultPositions (S i) !(sc defs (own fc i))
    resultPositions i (NTCon _ _ _ res)
        = do defs <- get Ctxt
             vals <- traverse (evalClosure defs . snd) res
             pure (mapMaybe (\(k, v) => map (\b => (b, k)) (given v))
                            (zip [0 .. length vals] vals))
    resultPositions i _ = pure []

    fields : List (Nat, Nat) -> (undetermined : List Name) ->
             (acc : List (Name, ClosedNF)) -> Nat -> ClosedNF ->
             Core (List (Name, ClosedNF), List Name)
    fields ps undet acc i (NBind fc x (Pi _ rig _ ty) sc)
        = do defs <- get Ctxt
             tynf <- evalClosure defs ty
             let acc' = if isErased rig then acc else (x, tynf) :: acc
             case lookup i ps >>= \k => argAt k args of
                  Just (_, arg) =>
                    do sc' <- sc defs arg
                       fields ps undet acc' (S i) sc'
                  Nothing =>
                    do sc' <- sc defs (own fc i)
                       let undet' = if isErased rig then binderName i :: undet else undet
                       fields ps undet' acc' (S i) sc'
    fields ps undet acc i _ = pure (reverse acc, undet)

||| The types of a constructor's run-time fields, at the type's arguments
||| `args`, with full names.
export
fieldTypes : {auto c : Ref Ctxt Defs} ->
             List (FC, ClosedClosure) -> GlobalDef -> Core (List ClosedTerm)
fieldTypes args cdef
    = do defs <- get Ctxt
         (fs, _) <- conFields args !(nf defs Env.empty (type cdef))
         traverse (\f => toFullNames !(quote defs Env.empty (snd f))) fs

-- Constructors flagged as a type of natural numbers' zero and successor.
natural : List GlobalDef -> Bool
natural [] = False
natural cdefs = all (any isNatFlag . flags) cdefs
  where
    isNatFlag : DefFlag -> Bool
    isNatFlag (ConType ZERO) = True
    isNatFlag (ConType SUCC) = True
    isNatFlag _ = False

||| Whether the type constructor `tn` is recursive: whether the run-time
||| fields of its constructors, at its own parameters, reach it again through
||| the declarations of the type constructors they mention, mutual recursion
||| included. A type constructor nested in itself at other arguments, as in
||| `Pair Bits64 (Pair Bits64 Bits64)`, is not recursion: the declaration of
||| `Pair` mentions no type constructor at all.
recursive : {auto c : Ref Ctxt Defs} -> Name -> Core Bool
recursive tn = reaches [] [tn]
  where
    isTyCon : Name -> Core Bool
    isTyCon n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure False
             pure $ case definition gdef of
                         TCon {} => True
                         _ => False

    -- The type constructors the run-time fields of `n`'s constructors
    -- mention, at `n`'s own parameters.
    fieldTyCons : Name -> Core (List Name)
    fieldTyCons n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
               | Nothing => pure []
             let TCon _ _ _ _ _ (Just cons) _ = definition gdef
               | _ => pure []
             cdefs <- catMaybes <$> traverse (\cn => lookupCtxtExact cn (gamma defs)) cons
             tys <- concat <$> traverse (fieldTypes []) cdefs
             let refs = concatMap (\t => keys (getRefs (UN Underscore) t)) tys
             traverse toFullNames !(filterM isTyCon refs)

    reaches : (visited : List Name) -> (todo : List Name) -> Core Bool
    reaches visited [] = pure False
    reaches visited (n :: todo)
        = if n `elem` visited then reaches visited todo else
            do ms <- fieldTyCons n
               if tn `elem` ms then pure True else reaches (n :: visited) (ms ++ todo)

||| What judging a type finds.
public export
data Judgement
  = ||| The type is flat, and its values take these registers.
    LaidOut Layout
  | ||| The type is made of erased arguments of the function being judged, so
    ||| it is known only in a specialisation of the function, where it is
    ||| judged in turn.
    Deferred
  | ||| The type is not flat, for this reason.
    Rejected NotFlatReason

-- The judgements of a value's parts in turn: the first rejection, else
-- deferred if any part is, else the parts' layouts concatenated.
concatJudgements : List Judgement -> Judgement
concatJudgements = go [] False
  where
    go : Layout -> (deferred : Bool) -> List Judgement -> Judgement
    go acc d [] = if d then Deferred else LaidOut acc
    go acc d (Rejected why :: _) = Rejected why
    go acc d (Deferred :: js) = go acc True js
    go acc d (LaidOut l :: js) = go (acc ++ l) d js

mutual
  ||| Judge a type: its layout if it is flat, or why it is not.
  judge : {auto c : Ref Ctxt Defs} ->
          Judging -> ClosedNF -> Core Judgement
  judge j (NPrimVal _ (PrT IntegerType)) = pure (Rejected (BoxedPrimitive IntegerType))
  judge j (NPrimVal _ (PrT StringType)) = pure (Rejected (BoxedPrimitive StringType))
  judge j (NPrimVal _ (PrT DoubleType)) = pure (LaidOut [Dbl])
  judge j (NPrimVal _ (PrT WorldType)) = pure (LaidOut [])
  judge j (NPrimVal _ (PrT _)) = pure (LaidOut [Word])
  judge j (NTCon _ n _ args)
      = if !(toFullNames n) == uniformType then pure (LaidOut [Uniform]) else judgeTyCon j n args
  judge j (NType {}) = pure (Rejected RuntimeType)
  judge j (NBind _ _ (Pi {}) _) = pure (Rejected FunctionType)
  judge j (NDelayed {}) = pure (Rejected LazyType)
  judge j (NErased {}) = pure (LaidOut [])
  judge j ty
      = do defs <- get Ctxt
           tm <- quote defs Env.empty ty
           pure (if mentions j.deferred tm then Deferred else Rejected StuckType)

  -- A type constructor `n` applied to `args`.
  judgeTyCon : {auto c : Ref Ctxt Defs} ->
               Judging -> Name -> List (FC, ClosedClosure) ->
               Core Judgement
  judgeTyCon j n args
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => pure (Rejected StuckType)
           let TCon _ _ _ tyflags _ (Just cons) _ = definition gdef
             | _ => pure (Rejected StuckType)
           tn <- toFullNames n
           cdefs <- catMaybes <$> traverse (\cn => lookupCtxtExact cn (gamma defs)) cons
           if natural cdefs then pure (Rejected (NaturalType tn)) else
             if !(recursive tn) then pure (Rejected (RecursiveType tn)) else
               case cdefs of
                    [] => pure (if tyflags.external then Rejected (ExternalType tn) else LaidOut [])
                    [cdef] => judgeCon j cdef args
                    _ => do js <- traverse (\cdef => judgeCon j cdef args) cdefs
                            pure (concatJudgements (LaidOut [Word] :: js))

  -- The layout of constructor `cdef`'s run-time fields, at the type's
  -- arguments `args`, or why one of them is not flat.
  judgeCon : {auto c : Ref Ctxt Defs} ->
             Judging -> GlobalDef -> List (FC, ClosedClosure) ->
             Core Judgement
  judgeCon j cdef args
      = do defs <- get Ctxt
           (fs, undet) <- conFields args !(nf defs Env.empty (type cdef))
           concatJudgements <$> traverse (field undet) fs
    where
      field : List Name -> (Name, ClosedNF) -> Core Judgement
      field undet (x, ty)
          = do Rejected why <- judge j ty
                 | other => pure other
               defs <- get Ctxt
               tm <- quote defs Env.empty ty
               pure $ Rejected $ case why of
                 StuckType => if mentions undet tm
                                 then UndeterminedField (fullname cdef) x
                                 else InField (fullname cdef) x tm why
                 _ => InField (fullname cdef) x tm why

||| The layout of a closed type, or why it is not flat. A type made of the
||| names in `deferred`, the erased arguments of a function being judged, is
||| deferred to the function's specialisations.
export
layout : {auto c : Ref Ctxt Defs} -> (deferred : List Name) -> ClosedNF -> Core Judgement
layout deferred = judge (MkJudging deferred)

||| `IO a` and its kind: a type with one constructor whose one run-time field
||| is a function. Its values are that function, so the function's arguments
||| extend a signature that returns it. The type's name comes back with the
||| function's type.
export
newtypeOverFunction : {auto c : Ref Ctxt Defs} -> ClosedNF -> Core (Maybe (Name, ClosedNF))
newtypeOverFunction (NTCon _ n _ args)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
           | Nothing => pure Nothing
         let TCon _ _ _ _ _ (Just [cn]) _ = definition gdef
           | _ => pure Nothing
         Just cdef <- lookupCtxtExact cn (gamma defs)
           | Nothing => pure Nothing
         ([(_, fnTy@(NBind _ _ (Pi {}) _))], _) <- conFields args !(nf defs Env.empty (type cdef))
           | _ => pure Nothing
         pure (Just (!(toFullNames n), fnTy))
newtypeOverFunction _ = pure Nothing

||| Check the signature of `fn`, a flat function: every run-time argument and
||| the result must be flat. What is not is the error.
|||
||| An argument of a function type is judged by its own signature, in turn:
||| each of its run-time arguments and its result must be flat, or a
||| function type judged the same way. A flat function at such an argument
||| has no form of its own, since the function is static; each call of it
||| gets a copy at the function it passes (`Flat.Translate`).
|||
||| A newtype over a function type at the result (`IO a`, over `(1 x :
||| %World) -> IORes a`) adds that function's arguments to the signature, as
||| does a synonym for a function type (`Op h a`), which normalising unfolds.
||| Two things are left to the function's specialisations, where they become
||| static or concrete: an auto-implicit argument (an interface constraint),
||| and a type made of the function's erased arguments (the token `m : h`
||| under `Memory h =>`).
|||
||| An error gives an argument's position among the explicit arguments, from
||| 1, for one that has no name.
export
checkFlatSignature : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core (Maybe FlatError)
checkFlatSignature fc fn
    = do defs <- get Ctxt
         Just ty <- lookupTyExact fn (gamma defs)
           | Nothing => undefinedName fc fn
         walk (MkJudging []) [] 0 !(nf defs Env.empty ty)
  where
    isAutoImplicit : PiInfo t -> Bool
    isAutoImplicit AutoImplicit = True
    isAutoImplicit _ = False

    mutual
      -- Why a type is not flat, a function type judged by its signature.
      reason : Judging -> ClosedNF -> Core (Maybe NotFlatReason)
      reason j ty@(NBind _ _ (Pi {}) _) = function j 0 [] ty
      reason j ty
          = case !(judge j ty) of
                 Rejected why => pure (Just why)
                 _ => pure Nothing

      -- Why a function type is not flat: its first argument or result that
      -- is not, with its position. A newtype over a function at the result
      -- (`IO a`) adds that function's arguments, once, as at the top.
      function : Judging -> (explicit : Nat) -> (unfolded : List Name) -> ClosedNF ->
                 Core (Maybe NotFlatReason)
      function j i ns (NBind bfc x (Pi _ rig pinfo aty) sc)
          = do defs <- get Ctxt
               let i' = case pinfo of
                             Explicit => S i
                             _ => i
               argNF <- evalClosure defs aty
               argWhy <- if isErased rig then pure Nothing else reason j argNF
               case argWhy of
                    Just why => pure (Just (InFunction (Just (i', x)) !(quote defs Env.empty argNF) why))
                    Nothing =>
                      do let j' = if isErased rig then { deferred $= (x ::) } j else j
                         function j' i' ns !(sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound x)))
      function j i ns res
          = do Just (n, fnTy) <- newtypeOverFunction res
                 | Nothing => result
               if n `elem` ns then result else function j i (n :: ns) fnTy
        where
          result : Core (Maybe NotFlatReason)
          result = do Just why <- reason j res
                        | Nothing => pure Nothing
                      defs <- get Ctxt
                      pure (Just (InFunction Nothing !(quote defs Env.empty res) why))

    -- Judge an argument (`Just`) or the result (`Nothing`); an auto-implicit
    -- argument is not rejected here.
    check : (autoImplicit : Bool) -> Judging -> Maybe (Nat, Name) -> ClosedNF -> Core (Maybe FlatError)
    check autoImplicit j arg ty
        = do Just why <- reason j ty
               | Nothing => pure Nothing
             if autoImplicit then pure Nothing else do
               defs <- get Ctxt
               tm <- quote defs Env.empty ty
               pure (Just (NotFlat fc !(toFullNames fn) arg tm why))

    -- `unfolded`: the newtypes over functions whose arguments the signature
    -- has taken already. Met again (a type such as `record Stream where next
    -- : Bits64 -> Stream`), one is judged as a value instead.
    walk : Judging -> (unfolded : List Name) -> (explicit : Nat) -> ClosedNF -> Core (Maybe FlatError)
    walk j ns i (NBind bfc x (Pi _ rig pinfo argTy) sc)
        = do defs <- get Ctxt
             let i' = case pinfo of
                           Explicit => S i
                           _ => i
             argNF <- evalClosure defs argTy
             argErr <- if isErased rig then pure Nothing
                          else check (isAutoImplicit pinfo) j (Just (i', x)) argNF
             case argErr of
                  Just err => pure (Just err)
                  Nothing =>
                    do let j' = if isErased rig then { deferred $= (x ::) } j else j
                       walk j' ns i' !(sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound x)))
    walk j ns i res
        = do Just (n, fnTy) <- newtypeOverFunction res
               | Nothing => result
             if n `elem` ns then result else walk j (n :: ns) i fnTy
      where
        result : Core (Maybe FlatError)
        result = check False j Nothing res
