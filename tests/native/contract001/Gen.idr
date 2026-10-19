-- What the lowering still checks of the runtime contract. Idris checks
-- each routine the runtime gives against its port where the runtime is
-- built (contract002); the lowering checks that a routine the runtime has
-- has a flat form, of the registers its port says. A routine is a flat
-- function of the runtime library, so its form's registers are its
-- parameters' and its result's.
--
-- The contract's port for `crash` takes two words, the message's address
-- and its length, and gives nothing, as if written
--
--   crash : (message, length : Bits64) -> Op Ordo ()
--
-- and `allocSlow`'s takes the bytes and gives the object's address. Here
-- the runtime's forms are stood in for by forms of the same names, with
-- bodies that are never run: only the check is shown. The stand-ins are
-- made from the routines themselves, one for each routine the runtime
-- has, of its port's registers, and each case changes or leaves out one.
--
-- So are the foreign functions the runtime implements, against `base`'s
-- declarations: `System.prim__exit : Int -> PrimIO ()`, whose C types are
-- an `Int` and the world, returning `IORes ()`, is implemented by
-- `Support.Foreign.System.prim__exit` of the same type, position by
-- position; one taking a `Bits64` where `base` says `Int` is refused.
module Main

import Compiler.VMCode
import Core.CompileExpr
import Core.FC
import Core.Name
import Core.TT
import Data.List
import Data.SortedMap
import Data.Vect
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Lower
import Native.Codegen.Platform
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Program
import Native.Flat.Exp
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.Port
import Native.Primitive
import Native.Routine
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.IntegerRoutine
import Native.Types.StringEnc
import Native.Types.StringRoutine

TestEnc : Enc
TestEnc = defaultEnc

-- The runtime's routines as a loaded runtime's record would give them
-- (`Native.Runtime.Routines.routines`), by the names its functions have.
runtimeStart, runtimeAllocSlow, runtimeAllocMutable, runtimeCrash : Name
runtimeStart = NS (runtimeModule "Start") (UN (Basic "start"))
runtimeAllocSlow = NS (runtimeModule "Space") (UN (Basic "allocSlow"))
runtimeAllocMutable = NS (runtimeModule "Space") (UN (Basic "allocMutable"))
runtimeCrash = NS (runtimeModule "System") (UN (Basic "crash"))

realised : Realised
realised =
  MkRealised [(runtimeStart, Start),
              (runtimeAllocSlow, AllocSlow), (runtimeAllocMutable, AllocMutable),
              (runtimeCrash, Crash)]
             Nothing Nothing empty empty empty empty

word : String -> FlatVar
word s = MkFlatVar (UN (Basic s)) (SPrim Bits64Type) [Word]

unit : Skeleton
unit = SCon (NS (mkNamespace "Builtin") (UN (Basic "Unit"))) []

||| A form of the name, with the parameters and the result's layout given.
form : Name -> List FlatVar -> Skeleton -> Layout -> FlatDef
form n ps sk lay = MkFlatDef n ps sk lay (FNone EmptyFC) EmptyFC

||| A register of the term IR as a stand-in's parameter or result: a word, or
||| a value as ordinary code holds it.
standIn : Ty TestEnc -> (Skeleton, Layout)
standIn Val = (SCon uniformType [SOther], [Uniform])
standIn _ = (SPrim Bits64Type, [Word])

||| A stand-in for every routine the runtime has, of its port's registers.
standIns : List FlatDef
standIns =
  [ form r.name (zipWith param [0 .. length r.params] r.params) (result r.results)
   (concatMap (snd . standIn) r.results)
           | r <- routines {enc = TestEnc} realised ]
  where
    param : Nat -> Ty TestEnc -> FlatVar
    param i t = MkFlatVar (UN (Basic ("p" ++ show i))) (fst (standIn t)) (snd (standIn t))

    result : List (Ty TestEnc) -> Skeleton
    result [t] = fst (standIn t)
    result _ = unit

||| The stand-ins with one replaced.
replacing : FlatDef -> List FlatDef
replacing f = f :: filter (\g => g.name /= f.name) standIns

||| The stand-ins with one left out.
without : Name -> List FlatDef
without n = filter (\g => g.name /= n) standIns

checkWith : String -> List FlatDef -> List (Name, VMDef) -> IO ()
checkWith what forms vmdefs = putStrLn $ what ++ ": " ++
  case lowerProgram TestEnc defaultPlatform realised forms [] empty vmdefs of
    Left err => err
    Right _ => "lowered"

check : String -> List FlatDef -> IO ()
check what forms = checkWith what forms []

||| `base`'s `System.prim__exit : Int -> PrimIO ()`, as VMCode has it.
exitForeign : (Name, VMDef)
exitForeign =
  (NS (mkNamespace "System") (UN (Basic "prim__exit")),
   MkVMForeign [] [CFInt, CFWorld] (CFIORes CFUnit))

||| The runtime's implementation of it, taking the argument given.
exitImplementation : Skeleton -> FlatDef
exitImplementation arg =
  form (NS (mkNamespace "Native.Support.Foreign.System") (UN (Basic "prim__exit")))
       [MkFlatVar (UN (Basic "status")) arg [Word], MkFlatVar (UN (Basic "w")) (SPrim WorldType) []]
       (SCon (NS (mkNamespace "PrimIO") (UN (Basic "IORes"))) [unit]) []

main : IO ()
main = do
  check "as given" standIns
  check "no crash" (without runtimeCrash)
  -- allocSlow (bytes, kind : Bits64) : Bits64
  check "allocSlow of two words"
    (replacing (form runtimeAllocSlow [word "bytes", word "kind"] (SPrim Bits64Type) [Word]))
  -- crash (message, length : Bits64) : Bits64
  check "crash with a result"
    (replacing (form runtimeCrash [word "message", word "length"] (SPrim Bits64Type) [Word]))
  -- prim__exit (status : Int) : PrimIO (), as base declares it
  checkWith "prim__exit as declared" (exitImplementation (SPrim IntType) :: standIns) [exitForeign]
  -- prim__exit (status : Bits64) : PrimIO ()
  checkWith "prim__exit of a Bits64" (exitImplementation (SPrim Bits64Type) :: standIns)
    [exitForeign]
