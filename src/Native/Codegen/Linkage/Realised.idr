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
||| The other entries are still read from records that give them: a
||| record's value is its constructor applied to its entries, in the fields'
||| order, which the code generator takes by position and rebuilds with the
||| same constructor. It names those records: `routines` of the runtime's
||| `Routines` and the string encoding's module's `strings`.
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
import Core.TT.Binder
import Core.TT.Term
import Data.List
import Data.SortedMap
import Data.Vect
import Data.Zippable
import Native.Codegen.Platform
import Native.Intrinsic
import Native.Port
import Native.Routines
import Native.Service
import Native.Types.Enc as Types
import Native.Types.StringRoutines as Types

%default covering

||| An entry as the loaded runtime realises it: the function, or the
||| extern, that is it.
public export
record Named (p : Port) where
  constructor MkNamed
  name : Name

||| The contract's entries, as the loaded runtime realises them.
public export
record Realised where
  constructor MkRealised
  ||| The generic runtime's routines.
  routines : Routines Named
  ||| The string encoding's routines, if the runtime has a module for it.
  strings : Maybe (Types.StringRoutines Named)
  ||| Each inline extern, with the intrinsic it is.
  externs : SortedMap Name Intrinsic
  ||| Each OS service's extern, with the platform's function for it.
  services : SortedMap Name Name

||| The contract as the loaded runtime realises it, for the platform and the
||| encodings, or what is missing.
export
realise : {auto c : Ref Ctxt Defs} -> Platform -> Types.Enc -> Core (Either String Realised)
realise platform enc = do
  Right rs <- fieldsOf (in' (RuntimeModule.runtimeModule "Routines") "routines") 4
    | Left e => pure (Left e)
  ss <- case RuntimeModule.stringModule enc.string of
    Just ns => map (map Just) (fieldsOf (in' ns "strings") 11)
    Nothing => pure (Right Nothing)
  let Right ss' = ss
    | Left e => pure (Left e)
  Just platformNs <- pure (OSService.platformModule platform)
    | Nothing => pure (Left ("the platform " ++ show platform ++ " has no OS services"))
  Right intrinsics <- entries "Native.Intrinsic" "allIntrinsics" Intrinsic.allIntrinsics [externTy] isExtern
    | Left e => pure (Left ("the runtime's inline externs: " ++ e))
  Right serviceExterns <- entries "Native.Service" "allServices" Service.allServices [externTy] isExtern
    | Left e => pure (Left ("the runtime's OS services: " ++ e))
  Right serviceFunctions <- entries "Native.Service" "allServices" Service.allServices [portTy] (inModule platformNs)
    | Left e => pure (Left ("the platform's OS services: " ++ e))
  let externs = fromList [ (n, i) | (n, _, i) <- intrinsics ]
      services = fromList [ (x, f) | (x, c, _) <- serviceExterns, (f, c', _) <- serviceFunctions, c == c' ]
  pure (Right (MkRealised (routinesOf rs) (map stringRoutinesOf ss') externs services))
  where
    ||| A definition of the root of a module.
    in' : Namespace -> String -> Name
    in' ns n = NS ns (UN (Basic n))

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

    ||| The definitions the context keeps whose type is the port of a
    ||| constructor of a contract's enumeration, `f (port c)` or `f addr (port
    ||| c)` for a head `f` of `heads`, each with its constructor's name and the
    ||| code generator's own constructor; exactly one of each, or which have
    ||| none or more. The constructors are the enumeration's list's
    ||| (`listName`, in the module `contract`): its term in the context and the
    ||| code generator's copy of it (`own`) are one declaration, so their
    ||| elements pair up whatever the order.
    entries : (contract, listName : String) -> (own : List a) -> (heads : List Name) ->
              (keep : Name -> GlobalDef -> Bool) -> Core (Either String (List (Name, Name, a)))
    entries contract listName own heads keep = do
      defs <- get Ctxt
      Just lg <- lookupCtxtExact (in' ns listName) (gamma defs)
        | Nothing => pure (Left ("the runtime has no " ++ show (in' ns listName)))
      listed <- case definition lg of
        PMDef _ _ (STerm _ tm) _ _ => elements <$> toFullNames tm
        _ => pure []
      let byConstructor = fromList (zip listed own)
      found <- catMaybes <$> traverse (entry defs byConstructor) !(allNames (gamma defs))
      let problems = mapMaybe (\c => case length (filter (\(_, c', _) => c' == c) found) of
                                        1 => Nothing
                                        0 => Just (show c ++ " has none")
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
                (Ref _ _ p, [Ref _ _ c]) => if p == in' ns "port" then Just c else Nothing
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

    ||| The `n` entries of the record a definition's value is, in the fields'
    ||| order: its constructor's last `n` arguments, after the record's
    ||| parameter.
    fieldsOf : Name -> (n : Nat) -> Core (Either String (Vect n Name))
    fieldsOf def n = do
      defs <- get Ctxt
      Just gdef <- lookupCtxtExact def (gamma defs)
        | Nothing => pure (Left ("the runtime has no " ++ show def))
      case definition gdef of
        PMDef _ _ (STerm _ tm) _ _ => do
          tm' <- toFullNames tm
          let args = snd (getFnArgs tm')
          pure $ case traverse entryName (drop (length args `minus` n) args) of
            Just ns => maybe (Left (show def ++ " is not a record of " ++ show n ++ " entries")) Right (toVect n ns)
            Nothing => Left ("an entry of " ++ show def ++ " is neither a function nor an extern")
        _ => pure (Left (show def ++ " is not a record's value"))
      where
        ||| The function or extern an entry is: under the lambdas Idris puts around
        ||| it for the port's implicit arguments, the head of what they apply.
        entryName : Term vars -> Maybe Name
        entryName (Bind _ _ (Lam {}) sc) = entryName sc
        entryName tm = case getFn tm of
          Ref _ _ n => Just n
          _ => Nothing

    ||| The records, rebuilt from their entries in the fields' order.
    routinesOf : Vect 4 Name -> Routines Named
    routinesOf [a1, a2, a3, a4] = MkRoutines (MkNamed a1) (MkNamed a2) (MkNamed a3) (MkNamed a4)

    stringRoutinesOf : Vect 11 Name -> Types.StringRoutines Named
    stringRoutinesOf [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] =
      Types.MkStringRoutines (MkNamed a1) (MkNamed a2) (MkNamed a3) (MkNamed a4) (MkNamed a5) (MkNamed a6)
        (MkNamed a7) (MkNamed a8) (MkNamed a9) (MkNamed a10) (MkNamed a11)
