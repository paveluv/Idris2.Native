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
||| The other entries are still read from records that give them: a
||| record's value is its constructor applied to its entries, in the fields'
||| order, which the code generator takes by position and rebuilds with the
||| same constructor. It names those records: `routines` of the runtime's
||| `Routines`, the string encoding's module's `strings`, the platform's
||| module's `services`, and the services' `externs` of `OS`.
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
import Native.Services
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
  Right externs <- intrinsicsByType
    | Left e => pure (Left e)
  Right xs <- fieldsOf (in' (RuntimeModule.runtimeModule "OS") "externs") 7
    | Left e => pure (Left e)
  Just platformNs <- pure (OSService.platformModule platform)
    | Nothing => pure (Left ("the platform " ++ show platform ++ " has no OS services"))
  Right fs <- fieldsOf (in' platformNs "services") 7
    | Left e => pure (Left e)
  let services =
        map (\(_ ** p) => p)
          (Services.serviceList (Services.zipServices (\x, f => (x.name, f.name)) (servicesOf xs) (servicesOf fs)))
  pure (Right (MkRealised (routinesOf rs) (map stringRoutinesOf ss') externs (fromList services)))
  where
    ||| A definition of the root of a module.
    in' : Namespace -> String -> Name
    in' ns n = NS ns (UN (Basic n))

    ||| Each inline extern of the loaded runtime, found by its type,
    ||| `ExternTy (port c)`, with the intrinsic `c` is; or which intrinsics
    ||| have no extern, or more than one.
    intrinsicsByType : Core (Either String (SortedMap Name Intrinsic))
    intrinsicsByType = do
      defs <- get Ctxt
      Just lg <- lookupCtxtExact (in' contract "allIntrinsics") (gamma defs)
        | Nothing => pure (Left ("the runtime has no " ++ show (in' contract "allIntrinsics")))
      listed <- case definition lg of
        PMDef _ _ (STerm _ tm) _ _ => elements <$> toFullNames tm
        _ => pure []
      let byConstructor = the (SortedMap Name Intrinsic) (fromList (zip listed Intrinsic.allIntrinsics))
      found <- traverse (externOf defs byConstructor) !(allNames (gamma defs))
      let found' = catMaybes found
          problems = mapMaybe (\c => case length (filter (\e => fst (snd e) == c) found') of
                                        1 => Nothing
                                        k => Just (show c ++ " has " ++ show k ++ " externs")) listed
      pure $ case problems of
        [] => Right (fromList (map (\(n, (_, i)) => (n, i)) found'))
        _ => Left ("the runtime's inline externs: " ++ concat (intersperse "; " problems))
      where
        contract : Namespace
        contract = mkNamespace "Native.Intrinsic"

        -- the elements of a list's term, `(::) {a} x xs` down to `Nil`
        elements : Term vars -> List Name
        elements tm = case getFnArgs tm of
          (Ref _ _ _, [_, Ref _ _ x, rest]) => x :: elements rest
          _ => []

        -- the extern a definition is, by its type, with its constructor and
        -- intrinsic, if it is one
        externOf : Defs -> SortedMap Name Intrinsic -> Name -> Core (Maybe (Name, (Name, Intrinsic)))
        externOf defs byConstructor n = do
          Just g <- lookupCtxtExact n (gamma defs)
            | Nothing => pure Nothing
          case definition g of
            ExternDef _ => do
              ty <- toFullNames (type g)
              n' <- toFullNames n
              pure $ case getFnArgs ty of
                (Ref _ _ f, [arg]) =>
                  if f /= NS (RuntimeModule.runtimeModule "PortTy") (UN (Basic "ExternTy")) then Nothing
                  else case getFnArgs arg of
                    (Ref _ _ pt, [Ref _ _ c]) =>
                      if pt /= in' contract "port" then Nothing
                      else map (\i => (n', (c, i))) (lookup c byConstructor)
                    _ => Nothing
                _ => Nothing
            _ => pure Nothing

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

    servicesOf : Vect 7 Name -> Services Named
    servicesOf [a1, a2, a3, a4, a5, a6, a7] =
      MkServices (MkNamed a1) (MkNamed a2) (MkNamed a3) (MkNamed a4) (MkNamed a5) (MkNamed a6) (MkNamed a7)
