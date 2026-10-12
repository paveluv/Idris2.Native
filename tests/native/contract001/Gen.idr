-- The runtime contract, checked: generated code calls the runtime's
-- routines by the signatures the contract declares, and a program is
-- lowered only if the runtime's routines have them. A routine is a flat
-- function of the runtime library, so its signature is its form's: the
-- registers of its parameters and of its result.
--
-- The contract declares `crash` as taking two words, the message's address
-- and its length, and returning nothing, as if written
--
--   crash : (message, length : Bits64) -> Op Heap ()
--
-- and `allocSlow` as taking the bytes and returning the object's address.
-- Here the runtime's forms are stood in for by forms of the same names,
-- with bodies that are never run: only the check is shown. The stand-ins
-- are made from the contract itself, one for each routine the runtime has,
-- with the declared signature, and each case changes or leaves out one.
--
-- The OS services are checked the same way, against the functions that
-- implement them on the platform: x86-64 Linux's `write` takes a handle,
-- an address and a count, and returns the bytes written.
--
-- So are the foreign functions the runtime implements, against `base`'s
-- declarations: `System.prim__exit : Int -> PrimIO ()`, whose C types are
-- an `Int` and the world, returning `IORes ()`, is implemented by
-- `Runtime.Foreign.System.prim__exit` of the same type, position by
-- position; one taking a `Bits64` where `base` says `Int` is refused.
module Main

import Compiler.Native.HeapObject
import Compiler.Native.IRCommon
import Compiler.Native.Linkage
import Compiler.Native.Lower
import Compiler.Native.Platform
import Compiler.Native.TermIR
import Compiler.VMCode
import Core.CompileExpr
import Core.FC
import Core.Name
import Core.TT
import Data.List
import Data.Vect
import Flat.Exp

TestEnc : Enc
TestEnc = defaultEnc

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

||| A stand-in for every routine the runtime has, of its declared signature.
standIns : List FlatDef
standIns = [ form r.name (zipWith param [0 .. length r.params] r.params) (result r.results) (concatMap (snd . standIn) r.results)
           | r <- routines {enc = TestEnc}, r.provided ]
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
  case lowerProgram TestEnc defaultPlatform forms [] vmdefs of
    Left err => err
    Right _ => "lowered"

check : String -> List FlatDef -> IO ()
check what forms = checkWith what forms []

||| `base`'s `System.prim__exit : Int -> PrimIO ()`, as VMCode has it.
exitForeign : (Name, VMDef)
exitForeign = (NS (mkNamespace "System") (UN (Basic "prim__exit")), MkVMForeign [] [CFInt, CFWorld] (CFIORes CFUnit))

||| The runtime's implementation of it, taking the argument given.
exitImplementation : Skeleton -> FlatDef
exitImplementation arg =
  form (NS (mkNamespace "Runtime.Foreign.System") (UN (Basic "prim__exit")))
       [MkFlatVar (UN (Basic "status")) arg [Word], MkFlatVar (UN (Basic "w")) (SPrim WorldType) []]
       (SCon (NS (mkNamespace "PrimIO") (UN (Basic "IORes"))) [unit]) []

main : IO ()
main = do
  check "as declared" standIns
  check "no crash" (without runtimeCrash)
  -- allocSlow (bytes, kind : Bits64) : Bits64
  check "allocSlow of two words" (replacing (form runtimeAllocSlow [word "bytes", word "kind"] (SPrim Bits64Type) [Word]))
  -- crash (message, length : Bits64) : Bits64
  check "crash with a result" (replacing (form runtimeCrash [word "message", word "length"] (SPrim Bits64Type) [Word]))
  -- write (handle, address, bytes : Bits64) : Bits64, on x86-64 Linux
  check "write as declared" (form linuxWrite [word "handle", word "address", word "bytes"] (SPrim Bits64Type) [Word] :: standIns)
  -- write (handle, address : Bits64) : Bits64
  check "write of two words" (form linuxWrite [word "handle", word "address"] (SPrim Bits64Type) [Word] :: standIns)
  -- prim__exit (status : Int) : PrimIO (), as base declares it
  checkWith "prim__exit as declared" (exitImplementation (SPrim IntType) :: standIns) [exitForeign]
  -- prim__exit (status : Bits64) : PrimIO ()
  checkWith "prim__exit of a Bits64" (exitImplementation (SPrim Bits64Type) :: standIns) [exitForeign]
  where
    linuxWrite : Name
    linuxWrite = NS (mkNamespace "Runtime.OS.LinuxX86_64") (UN (Basic "write"))
