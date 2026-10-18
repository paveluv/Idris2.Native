||| The contract as the loaded runtime realises it (`Realised`): for each
||| entry, the function or the extern that is it (`realise`), not named by
||| the code generator.
|||
||| An inline extern is found by its type alone: the runtime declares each
||| as `ExternTy (port c)` for its intrinsic `c` (`Native.Intrinsic`), which
||| Idris checks, and which the loaded context keeps as written. The
||| constructor `c` there is matched to the code generator's own by the
||| contract's list of every intrinsic: the list's term in the context and
||| the code generator's copy of it are one declaration, so their elements
||| pair up whatever the order. Each intrinsic must have exactly one extern.
|||
||| The OS services are found the same way, by their enumeration
||| (`Native.Service`): each extern, `ExternTy (port c)`, and the function of
||| the platform's module that implements it, `PortTy addr (port c)`, paired
||| by their constructor.
|||
||| The routines are found the same way (`Native.Routine`), each a function
||| `PortTy addr (port c)` of the runtime, and the string routines
||| (`Native.Types.StringRoutine`) in the string encoding's module.
|||
||| The backend's primitives are found the same way (`Native.Primitive`),
||| each a definition `FunctionTy (signature c)` of a module of
||| `Native.Primitive`, at most one of each: a program that imports none
||| uses none.
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
import Core.Name
import Core.Name.Namespace
import Core.TT
import Core.TT.Term
import Data.List
import Data.SortedMap
import Data.Zippable
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
  ||| Each OS service's extern, with the platform's function for it.
  services : SortedMap Name Name
  ||| Each of the backend's primitives the context defines, with the
  ||| primitive it is.
  primitives : SortedMap Name Primitive

||| A definition of the root of a module.
in' : Namespace -> String -> Name
in' ns n = NS ns (UN (Basic n))

||| The definitions the context keeps whose type is the port of a
||| constructor of a contract's enumeration, `f (port c)` or `f addr (port
||| c)` for a head `f` of `heads`, or its signature, `f (signature c)`,
||| each with its constructor's name and the code generator's own
||| constructor; exactly one of each if `required`, else at most one, or
||| which have none or more. The constructors are the enumeration's list's
||| (`listName`, in the module `contract`): its term in the context and the
||| code generator's copy of it (`own`) are one declaration, so their
||| elements pair up whatever the order. A context without the list has
||| none of them, which only an enumeration not `required` may.
entries : {auto c : Ref Ctxt Defs} -> (required : Bool) -> (contract, listName : String) -> (own : List a) -> (heads : List Name) ->
          (keep : Name -> GlobalDef -> Bool) -> Core (Either String (List (Name, Name, a)))
entries required contract listName own heads keep = do
  defs <- get Ctxt
  Just lg <- lookupCtxtExact (in' ns listName) (gamma defs)
    | Nothing => pure (if required then Left ("the runtime has no " ++ show (in' ns listName)) else Right [])
  listed <- case definition lg of
    PMDef _ _ (STerm _ tm) _ _ => elements <$> toFullNames tm
    _ => pure []
  let byConstructor = fromList (zip listed own)
  found <- catMaybes <$> traverse (entry defs byConstructor) !(allNames (gamma defs))
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
    portOf : Term vars -> Maybe Name
    portOf ty = case getFnArgs ty of
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
      n' <- toFullNames n
      if not (keep n' g) then pure Nothing else do
        ty <- toFullNames (type g)
        pure $ do
          c <- portOf ty
          i <- lookup c byConstructor
          pure (n', c, i)

||| The backend's primitives the context defines (`Native.Primitive`), each
||| by its type, `FunctionTy (signature c)`, in a module of
||| `Native.Primitive`: at most one of each.
primitives : {auto c : Ref Ctxt Defs} -> Core (Either String (List (Name, Name, Primitive)))
primitives = entries False "Native.Primitive" "allPrimitives" Primitive.allPrimitives [functionTy] inPrimitive
  where
    functionTy : Name
    functionTy = in' (mkNamespace "Native.Primitive") "FunctionTy"

    inPrimitive : Name -> GlobalDef -> Bool
    inPrimitive (NS ns _) _ = ns /= mkNamespace "Native.Primitive" && isParentOf (mkNamespace "Native.Primitive") ns
    inPrimitive _ _ = False

||| The names of the backend's primitives the context defines, for the flat
||| translation, which takes a call of one as the primitive's; none where
||| there are two of one, which `realise` reports.
export
primitiveNames : Ref Ctxt Defs -> Core (List Name)
primitiveNames c = either (const []) (map (\(n, _, _) => n)) <$> primitives

||| The contract as the loaded runtime realises it, for the platform and the
||| encodings, or what is missing.
export
realise : {auto c : Ref Ctxt Defs} -> Platform -> Types.Enc -> Core (Either String Realised)
realise platform enc = do
  Right rs <- entries True "Native.Routine" "allRoutines" Routine.allRoutines [portTy] runtimeOwn
    | Left e => pure (Left ("the runtime's routines: " ++ e))
  ss <- case RuntimeModule.stringModule enc.string of
    Just ns => map (map Just) (entries True "Native.Types.StringRoutine" "allStringRoutines"
                                 Types.StringRoutine.allStringRoutines [portTy] (inModule ns))
    Nothing => pure (Right Nothing)
  let Right ss' = ss
    | Left e => pure (Left ("the string encoding's routines: " ++ e))
  is <- case RuntimeModule.bignumModule enc.bignum of
    Just ns => map (map Just) (entries True "Native.Types.IntegerRoutine" "allIntegerRoutines"
                                 Types.IntegerRoutine.allIntegerRoutines [portTy] (inModule ns))
    Nothing => pure (Right Nothing)
  let Right is' = is
    | Left e => pure (Left ("the bignum encoding's routines: " ++ e))
  Just platformNs <- pure (OSService.platformModule platform)
    | Nothing => pure (Left ("the platform " ++ show platform ++ " has no OS services"))
  Right intrinsics <- entries True "Native.Intrinsic" "allIntrinsics" Intrinsic.allIntrinsics [externTy] isExtern
    | Left e => pure (Left ("the runtime's inline externs: " ++ e))
  Right serviceExterns <- entries True "Native.Service" "allServices" Service.allServices [externTy] isExtern
    | Left e => pure (Left ("the runtime's OS services: " ++ e))
  Right serviceFunctions <- entries True "Native.Service" "allServices" Service.allServices [portTy] (inModule platformNs)
    | Left e => pure (Left ("the platform's OS services: " ++ e))
  Right prims <- primitives
    | Left e => pure (Left ("the backend's primitives: " ++ e))
  let externs = fromList [ (n, i) | (n, _, i) <- intrinsics ]
      services = fromList [ (x, f) | (x, c, _) <- serviceExterns, (f, c', _) <- serviceFunctions, c == c' ]
  pure (Right (MkRealised (pairs rs) (map pairs ss') (map pairs is') externs services (fromList (pairs prims))))
  where
    externTy, portTy : Name
    externTy = in' (RuntimeModule.runtimeModule "PortTy") "ExternTy"
    portTy = in' (RuntimeModule.runtimeModule "PortTy") "PortTy"

    isExtern : Name -> GlobalDef -> Bool
    isExtern _ g = case definition g of
      ExternDef _ => True
      _ => False

    inModule : Namespace -> Name -> GlobalDef -> Bool
    inModule ns (NS ns' _) _ = ns' == ns
    inModule _ _ _ = False

    runtimeOwn : Name -> GlobalDef -> Bool
    runtimeOwn (NS ns _) _ = RuntimeModule.inRuntime ns
    runtimeOwn _ _ = False

    -- each entry's definition, with the code generator's constructor
    pairs : List (Name, Name, a) -> List (Name, a)
    pairs es = [ (n, x) | (n, _, x) <- es ]
