||| The contract as the loaded runtime realises it (`Realised`): for each
||| entry, the function or the extern that is it (`realise`), not named by
||| the code generator.
|||
||| An inline extern is found by its type among the runtime's externs, in
||| the modules where it declares them (`RuntimeModule.declaresExterns`):
||| the runtime declares each as `PortTy (port c)` for its intrinsic `c`
||| (`Native.Intrinsic`), which Idris checks, and which the loaded context
||| keeps as written. The constructor `c` there is matched to the code
||| generator's own by the contract's list of every intrinsic: the list's
||| term in the context and the code generator's copy of it are one
||| declaration, so their elements pair up whatever the order. Each
||| intrinsic must have exactly one extern. An extern of the runtime
||| outside those modules is refused as its module is built
||| (`checkExterns`), and outside the runtime an extern of a port's type is
||| an ordinary extern, not looked at: a program that declares one declares
||| no intrinsic, since the lowering knows an extern only as one found here.
|||
||| The OS services are found the same way, by their enumeration
||| (`Native.Service`): each extern, `PortTy (port c)`, among the runtime's,
||| and the function of the platform's module that implements it, of the
||| same type, paired by their constructor.
|||
||| The routines are found the same way (`Native.Routine`), each a function
||| `PortTy (port c)` of the runtime's core, and the string routines
||| (`Native.Types.StringRoutine`) in the string encoding's module. The
||| string routines the runtime's own code calls each have an extern among
||| the runtime's, as a service does, which the support tier's module of
||| the system's text declares (`RuntimeModule.textModule`), paired with the
||| encoding's function by their constructor.
|||
||| The backend's primitives are found the same way (`Native.Primitive`),
||| each a definition `FunctionTy (signature c)` of a module of
||| `Native.Primitive`, or, for one that reads an object, `PureLoad a
||| (signature c)` of the module of `Native.Types` that defines `a`; at
||| most one of each. Outside the modules of the two groups, a definition
||| of either type is an ordinary function, not looked at. The makers of an
||| object from words are found by their type too, `FromWords a`, each in
||| the module of `Native.Types` that defines `a`; outside the modules of
||| `Native.Types`, in those of `Native.Primitive` too, a definition of the
||| type is an ordinary function, not looked at. A program that imports
||| none of these uses none.
|||
||| So each entry is looked for only in the modules where it may be, by a
||| rule of the module's namespace alone, and only their definitions are
||| looked up (`named`), the runtime's externs once for every contract that
||| has them: a lookup decodes the definition it finds from its module's
||| TTC, and keeps it decoded, and most of the context's definitions are of
||| modules where no entry may be, the program's, its libraries' and most
||| of the runtime's.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Realised

import Native.Codegen.Linkage.OSService
import Native.Codegen.Linkage.RuntimeModule

import Core.Case.CaseTree
import Core.Context
import Core.Context.Context
import Core.Core
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Name.Scoped
import Core.TT.Term
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.Zippable
import Libraries.Data.NameMap
import Native.Codegen.Evaluate
import Native.Codegen.Platform
import Native.Intrinsic
import Native.Primitive
import Native.Routine
import Native.Service
import Native.Types.Enc as Types
import Native.Types.IntegerRoutine as Types
import Native.Types.StringRoutine as Types

%default covering

||| The contract's entries, as the loaded runtime realises them.
public export
record Realised where
  constructor MkRealised
  ||| Each routine of the runtime's core, with the function that is it.
  routines : List (Name, Routine)
  ||| Each routine of the string encoding's module, with the function that
  ||| is it, if the runtime has a module for the encoding.
  strings : Maybe (List (Name, Types.StringRoutine))
  ||| Each routine of the bignum encoding's module, with the function that is
  ||| it, if the runtime has a module for the encoding.
  integers : Maybe (List (Name, Types.IntegerRoutine))
  ||| Each inline extern, with the intrinsic it is.
  externs : SortedMap Name Intrinsic
  ||| Each extern bound to a function the program's choices pick: each OS
  ||| service's, with the platform's function for it, and each of the
  ||| string encoding's (`StringRoutine`'s text), with the encoding's.
  services : SortedMap Name Name
  ||| Each of the backend's primitives the context defines, with the
  ||| primitive it is.
  primitives : SortedMap Name Primitive
  ||| Each maker of an object from words the context defines
  ||| (`Types.FromWords`).
  makers : SortedSet Name

||| A definition of the root of a module.
in' : Namespace -> String -> Name
in' ns n = NS ns (UN (Basic n))

||| The full names of the context's entries of the modules whose namespaces
||| pass a rule, in the order the context added the entries in, none looked
||| up; a name of no module passes no rule. The context's map from full
||| names to entries (`resolvedAs`) holds every entry's name and decodes no
||| definition to give it; Idris's list of the names (`allNames`) looks up
||| every entry, which decodes the whole context, and leaves out the first.
||| The order is kept because the contract's lists follow it, and the image
||| follows them. The rule is given every entry's namespace, so it is made
||| before the walk, with the namespaces it compares (`under`,
||| `RuntimeModule.inCore`), and given as made, not made at each name.
named : (rule : Namespace -> Bool) -> Context -> List Name
named rule ctxt =
  map fst (sortBy (comparing snd) (filter (inModule . fst) (NameMap.toList (resolvedAs ctxt))))
  where
    inModule : Name -> Bool
    inModule (NS ns _) = rule ns
    inModule _ = False

||| The definitions the context keeps whose type is the port of a
||| constructor of a contract's enumeration, `f ... (port c)` for a head `f`
||| of `heads`, or its signature, `f ... (signature c)`, the last argument,
||| each with its constructor's name and the code generator's own
||| constructor; exactly one of each if `required`, else at most one, or
||| which have none or more. Of the context's definitions, only the
||| `candidates` are looked up, those of the modules where the entries may
||| be (`named`), in the context's order. The constructors are the
||| enumeration's list's (`listName`, in the module `contract`): its term
||| in the context and the code generator's copy of it (`own`) are one
||| declaration, so their elements pair up whatever the order. A context
||| without the list has none of them, which only an enumeration not
||| `required` may.
entries : {auto c : Ref Ctxt Defs} -> (required : Bool) -> (contract, listName : String) ->
          (own : List a) -> (heads : List Name) -> (candidates : List Name) ->
          Core (Either String (List (Name, Name, a)))
entries required contract listName own heads candidates = do
  defs <- get Ctxt
  Just lg <- lookupCtxtExact (in' ns listName) (gamma defs)
    | Nothing =>
      pure (if required then Left ("the runtime has no " ++ show (in' ns listName)) else Right [])
  listed <- case definition lg of
    PMDef _ _ (STerm _ tm) _ _ => elements <$> toFullNames tm
    _ => pure []
  let byConstructor = fromList (zip listed own)
  found <- catMaybes <$> traverse (entry defs byConstructor) candidates
  let problems = mapMaybe (\c => case length (filter (\(_, c', _) => c' == c) found) of
                                    1 => Nothing
                                    0 => if required then Just (show c ++ " has none") else Nothing
                                    k => Just (show c ++ " has " ++ show k)) listed
  pure (if null problems then Right found else Left (concat (intersperse "; " problems)))
  where
    ns : Namespace
    ns = mkNamespace contract

    -- the elements of a list's term, `(::) {a} x xs` down to `Nil`
    elements : Term vars -> List Name
    elements tm = case getFnArgs tm of
      (Ref _ _ _, [_, Ref _ _ x, rest]) => x :: elements rest
      _ => []

    -- the constructor a type is the port of, if it is one
    typePort : Term vars -> Maybe Name
    typePort ty = case getFnArgs ty of
      (Ref _ _ f, args) =>
        if not (f `elem` heads) then Nothing
        else case reverse args of
          (arg :: _) => case getFnArgs arg of
            (Ref _ _ p, [Ref _ _ c]) =>
              if p == in' ns "port" || p == in' ns "signature" then Just c else Nothing
            _ => Nothing
          [] => Nothing
      _ => Nothing

    -- a definition of the port of a constructor, with it
    entry : Defs -> SortedMap Name a -> Name -> Core (Maybe (Name, Name, a))
    entry defs byConstructor n = do
      Just g <- lookupCtxtExact n (gamma defs)
        | Nothing => pure Nothing
      ty <- toFullNames (type g)
      pure $ do
        c <- typePort ty
        i <- lookup c byConstructor
        pure (n, c, i)

||| Strictly under a group of modules. The group's namespace is made once,
||| with the rule (`under g`), not at each namespace the rule is given.
under : String -> Namespace -> Bool
under g = let root = mkNamespace g in \ns => ns /= root && isParentOf root ns

||| Whether a type's head is defined in the module: `Bytes` of `PureLoad
||| Bytes ...` in `Native.Types.Bytes`. A primitive that reads an object of
||| a type, or a maker of one, is defined in the type's module, which
||| answers for the type's statements.
definesType : Namespace -> Term vars -> Bool
definesType ns t = case getFnArgs t of
  (Ref _ _ (NS ns' _), _) => ns' == ns
  _ => False

||| The backend's primitives the context defines (`Native.Primitive`), at
||| most one of each: a function of words, by its type `FunctionTy
||| (signature c)`, in a module of `Native.Primitive`; or one that reads an
||| object of a type `a`, by its type `PureLoad a (signature c)`, in the
||| module of `Native.Types` that defines `a`. A definition of either head
||| elsewhere in the modules of the two groups is a problem, as two of one
||| primitive are; outside them, it is an ordinary function, not looked at.
primitives : {auto c : Ref Ctxt Defs} -> Core (Either String (List (Name, Name, Primitive)))
primitives = do
  defs <- get Ctxt
  Right found <- entries False "Native.Primitive" "allPrimitives" Primitive.allPrimitives
                   [functionTy, pureLoad] (named inGroups (gamma defs))
    | Left e => pure (Left e)
  misplaced <- catMaybes <$> traverse (\(n, _, _) => place n) found
  pure (if null misplaced then Right found else Left (concat (intersperse "; " misplaced)))
  where
    functionTy : Name
    functionTy = in' (mkNamespace "Native.Primitive") "FunctionTy"

    pureLoad : Name
    pureLoad = in' (mkNamespace "Native.Types.PureLoad") "PureLoad"

    -- a module of either group, the groups' namespaces made once, with the
    -- rule; where each head may be, `place` says
    inGroups : Namespace -> Bool
    inGroups = let inPrimitive = under "Native.Primitive"
                   inTypes = under "Native.Types" in
               \ns => inPrimitive ns || inTypes ns

    -- what is wrong with where a primitive is defined, if anything
    place : Name -> Core (Maybe String)
    place n@(NS ns _) = do
      defs <- get Ctxt
      Just g <- lookupCtxtExact n (gamma defs)
        | Nothing => pure Nothing
      ty <- toFullNames (type g)
      pure $ case getFnArgs ty of
        (Ref _ _ f, args) =>
          if f == functionTy
            then if under "Native.Primitive" ns then Nothing
                 else Just (show n ++ " is a primitive outside the modules of Native.Primitive")
            else case args of
              (a :: _) => if definesType ns a then Nothing
                          else Just (show n ++ " reads a type it is not defined with")
              [] => Just (show n ++ " reads no type")
        _ => Nothing
    place _ = pure Nothing

||| The definitions the flat translation takes a call of as a primitive's:
||| the backend's primitives the context defines. Two of one primitive, or
||| one defined in the modules of its groups where it may not be, end the
||| compilation here, with what is wrong, before any translation would take
||| its calls for calls of functions.
export
flatPrimitives : Ref Ctxt Defs -> Core (List Name)
flatPrimitives c = do
  Right ps <- primitives
    | Left e => throw (GenericMsg EmptyFC ("the backend's primitives: " ++ e))
  pure (map (\(n, _, _) => n) ps)

||| The check of a module as it is built, before its TTC is written: an
||| extern of the runtime that the module declares outside the modules
||| where the runtime declares its externs (`RuntimeModule.declaresExterns`)
||| is an error, at the extern. The contract looks for every extern only
||| there, so one elsewhere would be no entry of it but an ordinary extern,
||| which the lowering knows as none of the contract's, and each call of
||| which would fail as it ran. The module's own definitions are the names
||| its TTC is to keep (`toSave`), held as elaborated, so none is decoded
||| to be checked; a module outside the runtime declares none of the
||| runtime's, and is not looked at.
export
checkExterns : Ref Ctxt Defs -> Core ()
checkExterns c = do
  defs <- get Ctxt
  if not (RuntimeModule.inRuntime (currentNS defs)) then pure () else
    traverse_ (misplaced defs) (keys (toSave defs))
  where
    -- an error if the name is an extern of the runtime outside its modules
    -- of externs
    misplaced : Defs -> Name -> Core ()
    misplaced defs n@(NS ns _) =
      if not (RuntimeModule.inRuntime ns) || RuntimeModule.declaresExterns ns then pure () else do
        Just g <- lookupCtxtExact n (gamma defs)
          | Nothing => pure ()
        case definition g of
          ExternDef _ =>
            throw
              (GenericMsg (location g)
                (show n ++ " is an extern of the runtime outside its core and "
                 ++ show RuntimeModule.textModule ++ ", where the runtime declares its externs"
                 ++ " and the code generator looks for them"))
          _ => pure ()
    misplaced _ _ = pure ()

||| The contract as the loaded runtime realises it, for the platform and the
||| encodings, or what is missing.
export
realise : {auto c : Ref Ctxt Defs} -> Platform -> Types.Enc -> Core (Either String Realised)
realise platform enc = do
  defs <- get Ctxt
  -- the runtime's externs, every contract's, found once for the three
  -- contracts that have externs, each of which takes its own by their port
  externs <- catMaybes <$> traverse (extern defs) (named RuntimeModule.declaresExterns (gamma defs))
  Right rs <- entries True "Native.Routine" "allRoutines" Routine.allRoutines [portTy]
                (named RuntimeModule.inCore (gamma defs))
    | Left e => pure (Left ("the runtime's routines: " ++ e))
  ss <- case RuntimeModule.stringModule enc.string of
    Just ns => map (map Just) (entries True "Native.Types.StringRoutine" "allStringRoutines"
                                 Types.StringRoutine.allStringRoutines [portTy]
                                 (named (== ns) (gamma defs)))
    Nothing => pure (Right Nothing)
  let Right ss' = ss
    | Left e => pure (Left ("the string encoding's routines: " ++ e))
  is <- case RuntimeModule.bignumModule enc of
    Just ns => map (map Just) (entries True "Native.Types.IntegerRoutine" "allIntegerRoutines"
                                 Types.IntegerRoutine.allIntegerRoutines [portTy]
                                 (named (== ns) (gamma defs)))
    Nothing => pure (Right Nothing)
  let Right is' = is
    | Left e => pure (Left ("the bignum encoding's routines: " ++ e))
  Just platformNs <- pure (OSService.platformModule platform)
    | Nothing => pure (Left ("the platform " ++ show platform ++ " has no OS services"))
  Right intrinsics <- entries True "Native.Intrinsic" "allIntrinsics" Intrinsic.allIntrinsics
    [portTy] externs
    | Left e => pure (Left ("the runtime's inline externs: " ++ e))
  Right serviceExterns <- entries True "Native.Service" "allServices" Service.allServices [portTy]
    externs
    | Left e => pure (Left ("the runtime's OS services: " ++ e))
  Right serviceFunctions <- entries True "Native.Service" "allServices" Service.allServices [portTy]
    (named (== platformNs) (gamma defs))
    | Left e => pure (Left ("the platform's OS services: " ++ e))
  Right textExterns <- entries False "Native.Types.StringRoutine" "allStringRoutines"
    Types.StringRoutine.allStringRoutines [portTy] externs
    | Left e => pure (Left ("the runtime's externs of the string encoding: " ++ e))
  Right prims <- primitives
    | Left e => pure (Left ("the backend's primitives: " ++ e))
  Right ms <- makers
    | Left e => pure (Left ("the makers of objects from words: " ++ e))
  let externs = fromList [ (n, i) | (n, _, i) <- intrinsics ]
      services =
        fromList ([ (x, f) | (x, c, _) <- serviceExterns, (f, c', _) <- serviceFunctions, c == c' ]
                           ++ [ (x, f) | (x, c, _) <- textExterns,
                               (f, c', _) <- fromMaybe [] ss', c == c' ])
  pure
    (Right
      (MkRealised (pairs rs) (map pairs ss') (map pairs is') externs services
       (fromList (pairs prims)) (fromList ms)))
  where
    portTy : Name
    portTy = in' (RuntimeModule.runtimeModule "PortTy") "PortTy"

    -- the name, if the context's definition of it is an extern
    extern : Defs -> Name -> Core (Maybe Name)
    extern defs n = do
      Just g <- lookupCtxtExact n (gamma defs)
        | Nothing => pure Nothing
      pure (case definition g of
              ExternDef _ => Just n
              _ => Nothing)

    -- each entry's definition, with the code generator's constructor
    pairs : List (Name, Name, a) -> List (Name, a)
    pairs es = [ (n, x) | (n, _, x) <- es ]

    ||| The makers of an object from words the context defines
    ||| (`Types.FromWords`): each a definition of a type `FromWords a`, in the
    ||| module of `Native.Types` that defines `a`, which answers for the mark's
    ||| statement. One in another module of `Native.Types` is a problem, as is
    ||| one Idris inlines at each use, whose calls are then its body, where the
    ||| evaluation would take the maker's call to mean its object. Outside the
    ||| modules of `Native.Types`, a definition of the type is an ordinary
    ||| function, not looked at.
    makers : Core (Either String (List Name))
    makers = do
      defs <- get Ctxt
      -- the mark's name, made once for the walk over the names
      let fromWords = in' (mkNamespace "Native.Types.FromWords") "FromWords"
      found <- catMaybes <$>
                 traverse (maker defs fromWords) (named (under "Native.Types") (gamma defs))
      let problems = mapMaybe snd found
      pure (if null problems then Right (map fst found)
            else Left (concat (intersperse "; " problems)))
      where
        -- a maker the context defines, by the mark's name, with what is
        -- wrong with it, if anything
        maker : Defs -> (fromWords : Name) -> Name -> Core (Maybe (Name, Maybe String))
        maker defs fromWords n@(NS ns _) = do
          Just g <- lookupCtxtExact n (gamma defs)
            | Nothing => pure Nothing
          ty <- toFullNames (type g)
          pure $ case getFnArgs ty of
            (Ref _ _ f, a :: _) =>
              if f /= fromWords then Nothing
              else Just (n, if not (definesType ns a)
                              then Just (show n ++ " makes a type it is not defined with")
                            else if Evaluate.inlined g
                              then Just (show n ++ " is a maker Idris inlines at each use,"
                                         ++ " so no call of it is left to mean its object: "
                                         ++ Evaluate.inliningFix g)
                            else Nothing)
            _ => Nothing
        maker _ _ _ = pure Nothing
