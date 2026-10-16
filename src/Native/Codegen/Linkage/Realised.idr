||| The contract as the loaded runtime realises it (`Realised`): for each
||| entry, the function or the extern that is it, read from the records that
||| give them (`realise`), not named by the code generator.
|||
||| A record's value is its constructor applied to its entries, in the
||| fields' order. The code generator takes them by position and rebuilds
||| the record with the same constructor, so a field is the same field on
||| both sides, and Idris has checked each entry against its field's port
||| where the record was built. What the code generator names is the
||| records: `routines` of the runtime's `Routines`, the string encoding's
||| module's `strings`, the platform's module's `services`, and the
||| contract's `intrinsics` and `externs`.
|||
||| Part of what generated code, the runtime and the linker agree on
||| (`Native.Codegen.Linkage.Routine` says what it is).
module Native.Codegen.Linkage.Realised

import Native.Codegen.Linkage.InlineExtern
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
import Native.Codegen.Platform
import Native.Intrinsics
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
  ||| Each inline extern, with the instruction it stands for.
  externs : SortedMap Name InlineExtern
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
  Right is <- fieldsOf (in' (mkNamespace "Native.Intrinsics") "intrinsics") 23
    | Left e => pure (Left e)
  Right xs <- fieldsOf (in' (mkNamespace "Native.Services") "externs") 7
    | Left e => pure (Left e)
  Just platformNs <- pure (OSService.platformModule platform)
    | Nothing => pure (Left ("the platform " ++ show platform ++ " has no OS services"))
  Right fs <- fieldsOf (in' platformNs "services") 7
    | Left e => pure (Left e)
  let externs =
        map (\(_ ** p) => p)
          (Intrinsics.intrinsicList
           (Intrinsics.zipIntrinsics (\e, l => (e.name, l)) (intrinsicsOf is) InlineExtern.lowerings))
      services =
        map (\(_ ** p) => p)
          (Services.serviceList (Services.zipServices (\x, f => (x.name, f.name)) (servicesOf xs) (servicesOf fs)))
  pure (Right (MkRealised (routinesOf rs) (map stringRoutinesOf ss') (fromList externs) (fromList services)))
  where
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

    intrinsicsOf : Vect 23 Name -> Intrinsics Named
    intrinsicsOf [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
                  a22, a23] =
      MkIntrinsics (MkNamed a1) (MkNamed a2) (MkNamed a3) (MkNamed a4) (MkNamed a5) (MkNamed a6) (MkNamed a7)
                   (MkNamed a8) (MkNamed a9) (MkNamed a10) (MkNamed a11) (MkNamed a12) (MkNamed a13) (MkNamed a14)
                   (MkNamed a15) (MkNamed a16) (MkNamed a17) (MkNamed a18) (MkNamed a19) (MkNamed a20) (MkNamed a21)
                   (MkNamed a22) (MkNamed a23)

    ||| A definition of the root of a module.
    in' : Namespace -> String -> Name
    in' ns n = NS ns (UN (Basic n))
