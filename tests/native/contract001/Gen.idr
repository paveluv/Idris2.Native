-- What the code generator still checks of the runtime contract. Idris
-- checks each routine the runtime gives against its port where the
-- runtime is built (contract002); the code generator checks, before it
-- lowers a program, that a routine the runtime has has a flat form, of
-- the registers its port says (`checkRoutines`), among the runtime's
-- forms, whichever routines the program calls: in the routines' cases
-- here, a program of no functions, which calls none. A routine is a flat
-- function of the runtime library, so its form's registers are its
-- parameters' and its result's. The lowering takes the check's evidence
-- (`RoutinesChecked`), so no program is lowered unchecked, and checks no
-- routine itself: a program that calls none is lowered with none of the
-- routines' forms.
--
-- The contract's port for `crash` takes the message's address, the
-- runtime's byte address, and its length in bytes, and gives nothing, as
-- if written
--
--   crash : (message : ByteAddr) -> (bytes : Bits64) -> Op Ordo ()
--
-- and `allocSlow`'s takes the bytes and gives the room's address. Here
-- the runtime's forms are stood in for by forms of the same names, with
-- bodies that are never run: only the check is shown. The stand-ins are
-- made from the routines themselves, one for each routine the runtime
-- has, of its port's registers, and each case changes or leaves out one.
--
-- The lowering checks the foreign functions the runtime implements
-- against `base`'s declarations: `System.prim__exit : Int -> PrimIO ()`,
-- whose C types are an `Int` and the world, returning `IORes ()`, is
-- implemented by `Support.Foreign.System.prim__exit` of the same type,
-- position by position; one taking a `Bits64` where `base` says `Int` is
-- refused.
--
-- And it checks the static objects it is given, which the values of
-- constants marked static are laid out as: an object that holds another
-- holds that one's address, which the lowering finds among the program's
-- statics, and one it does not find stops it, with the error naming the
-- holder. As if a constant were written `pair = (7, "seven")`, its object
-- holds the fixnum 7 and the address of the string's object; given
-- without the string's object, it is refused.
--
-- A string or `Integer` routine, which the lowering calls by its name,
-- is declared outside a program not lowered with its form, and a call of
-- it stops the compile: the rendering finds no function of the program
-- for it, and refuses it, naming the routine. (The routines the
-- rendering and the seed reach by symbol, `start`, `allocSlow`,
-- `allocMutable` and `crash`, are not declared: their symbols are
-- defined at their forms.) The program's main expression is one call,
--
--   length "abc"
--
-- which the lowering makes a call of the string encoding's routine, as
-- if written `Native.Support.String.Utf8.length "abc"`. It is lowered,
-- its registers allocated, cut to what it reaches, as the code generator
-- cuts a program, and rendered: with every routine's form, it is
-- rendered; with every routine's but that one's, it is refused.
module Main

import Compiler.VMCode
import Core.CompileExpr
import Core.FC
import Core.Name
import Core.TT
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Native.Codegen.ConstantWord
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Linkage.Sym
import Native.Codegen.LocatedIR.Program
import Native.Codegen.LocatedIR.Reach
import Native.Codegen.Lower
import Native.Codegen.Platform
import Native.Codegen.RegAlloc
import Native.Codegen.StaticRead
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Program
import Native.Codegen.X86.Render
import Native.Codegen.X86.Target
import Native.Flat.Exp
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.Port
import Native.Primitive
import Native.Rep
import Native.Routine
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.IntegerRoutine
import Native.Types.StringEnc
import Native.Types.StringRoutine

TestEnc : Enc
TestEnc = defaultEnc

-- The runtime's routines as a loaded runtime's record would give them
-- (`Native.Runtime.Routines.routines`), by the names its functions have,
-- and one routine of its string encoding's module, `length`.
runtimeStart, runtimeAllocSlow, runtimeAllocMutable, runtimeCrash, utf8Length : Name
runtimeStart = NS (runtimeModule "Start") (UN (Basic "start"))
runtimeAllocSlow = NS (runtimeModule "Space") (UN (Basic "allocSlow"))
runtimeAllocMutable = NS (runtimeModule "Space") (UN (Basic "allocMutable"))
runtimeCrash = NS (runtimeModule "System") (UN (Basic "crash"))
utf8Length = NS (supportModule "String.Utf8") (UN (Basic "length"))

realised : Realised
realised =
  MkRealised [(runtimeStart, Start),
              (runtimeAllocSlow, AllocSlow), (runtimeAllocMutable, AllocMutable),
              (runtimeCrash, Crash)]
             (Just [(utf8Length, Length)]) Nothing empty empty empty empty

word : String -> FlatVar
word s = MkFlatVar (UN (Basic s)) (SPrim Bits64Type) [Word]

unit : Skeleton
unit = SCon (NS (mkNamespace "Builtin") (UN (Basic "Unit"))) []

||| A form of the name, with the parameters and the result's layout given.
form : Name -> List FlatVar -> Skeleton -> Layout -> FlatDef
form n ps sk lay = MkFlatDef n ps sk lay (FNone EmptyFC) EmptyFC

||| A register of the term IR as a stand-in's parameter or result: a word, a
||| value as ordinary code holds it, or the runtime's byte address, which is
||| an address, not its word.
standIn : Ty TestEnc -> (Skeleton, Layout)
standIn Val = (SCon uniformType [SOther], [Uniform])
standIn Ty.ByteAddr = (SCon byteAddrType [], [Rep.ByteAddr])
standIn _ = (SPrim Bits64Type, [Word])

||| A parameter of the name, in a register of the type, as a stand-in's.
parameter : String -> Ty TestEnc -> FlatVar
parameter s t = MkFlatVar (UN (Basic s)) (fst (standIn t)) (snd (standIn t))

||| A stand-in for every routine the runtime has, of its port's registers.
standIns : List FlatDef
standIns =
  [ form r.name (zipWith param [0 .. length r.params] r.params) (result r.results)
   (concatMap (snd . standIn) r.results)
           | r <- routines {enc = TestEnc} realised ]
  where
    param : Nat -> Ty TestEnc -> FlatVar
    param i = parameter ("p" ++ show i)

    result : List (Ty TestEnc) -> Skeleton
    result [t] = fst (standIn t)
    result _ = unit

||| The stand-ins with one replaced.
replacing : FlatDef -> List FlatDef
replacing f = f :: filter (\g => g.name /= f.name) standIns

||| The stand-ins with one left out.
without : Name -> List FlatDef
without n = filter (\g => g.name /= n) standIns

||| The foreign function and the runtime's flat function that implements
||| it, as the code generator binds them.
exitBinding : (Name, Name)
exitBinding =
  (NS (mkNamespace "System") (UN (Basic "prim__exit")),
   NS (mkNamespace "Native.System.Foreign.System") (UN (Basic "prim__exit")))

||| What the code generator makes of a program, as it compiles one: the
||| routines checked against their ports among the runtime's forms
||| (`runtime`), then the program lowered with the check's evidence and
||| with the forms it is given (`program`), the static objects, the foreign
||| functions the runtime implements by flat functions, and its VMCode.
lowered : (runtime, program : List FlatDef) -> SortedMap Name StaticPlan -> List (Name, Name) ->
          List (Name, VMDef) -> Either String (TermProgram TestEnc)
lowered runtime program objects flat vmdefs = do
  checked <- checkRoutines TestEnc realised (\n => find (\fd => fd.name == n) runtime)
  lowerProgram TestEnc defaultPlatform realised checked program [] empty objects [] flat []
    vmdefs

||| The program lowered (`lowered`), or why it is not.
compile : (runtime, program : List FlatDef) -> SortedMap Name StaticPlan -> List (Name, Name) ->
          List (Name, VMDef) -> String
compile runtime program objects flat vmdefs =
  either id (const "lowered") (lowered runtime program objects flat vmdefs)

||| The program lowered (`lowered`, with no static objects and no foreign
||| function), its registers allocated, cut to what its entry and the
||| routines the seed reaches by symbol reach, as the code generator cuts
||| it, and rendered; or why it is not.
rendered : (runtime, program : List FlatDef) -> List (Name, VMDef) -> String
rendered runtime program vmdefs = either id (const "rendered") $ do
  (_ ** term) <- lowered runtime program empty [] vmdefs
  let ir = reach (\n => isJust (routineSymbol {enc = TestEnc} realised n)) (allocRegs x86_64 term)
  ignore (render TestEnc realised ir)

||| The program compiled with these forms as the runtime's, every one of
||| them given to the lowering.
checkWith : String -> List FlatDef -> List (Name, VMDef) -> IO ()
checkWith what forms vmdefs =
  putStrLn $ what ++ ": " ++ compile forms forms empty [exitBinding] vmdefs

check : String -> List FlatDef -> IO ()
check what forms = checkWith what forms []

||| The objects of `pair = (7, "seven")`, by their names: the pair's, of
||| constructor 1, as Idris makes a pair (`_builtin.CONS`, of the one
||| constructor of two fields), named as the first object a value is laid
||| out as; and the string's, named as every string constant's object is.
pairObject, sevenObject : Name
pairObject = NS (mkNamespace "_native") (UN (Basic "static 0"))
sevenObject = NS (mkNamespace "_native") (UN (Basic ("string_" ++ show "seven")))

||| The compile of no function, with the stand-ins and these static objects.
checkObjects : String -> SortedMap Name StaticPlan -> IO ()
checkObjects what objects = putStrLn $ what ++ ": " ++ compile standIns standIns objects [] []

||| `base`'s `System.prim__exit : Int -> PrimIO ()`, as VMCode has it.
exitForeign : (Name, VMDef)
exitForeign =
  (NS (mkNamespace "System") (UN (Basic "prim__exit")),
   MkVMForeign [] [CFInt, CFWorld] (CFIORes CFUnit))

||| The runtime's implementation of it, taking the argument given.
exitImplementation : Skeleton -> FlatDef
exitImplementation arg =
  form (snd exitBinding)
       [MkFlatVar (UN (Basic "status")) arg [Word], MkFlatVar (UN (Basic "w")) (SPrim WorldType) []]
       (SCon (NS (mkNamespace "PrimIO") (UN (Basic "IORes"))) [unit]) []

||| The main expression `length "abc"`, as VMCode has it: the string in a
||| register, then the primitive string length of it, which the lowering
||| makes a call of the string routine.
lengthMain : (Name, VMDef)
lengthMain =
  (mainExpression, MkVMFun [] [MKCONSTANT (Loc 0) (Str "abc"), OP RVal StrLength [Loc 0]])

main : IO ()
main = do
  check "as given" standIns
  check "no crash" (without runtimeCrash)
  -- allocSlow (bytes, kind : Bits64) : Bits64
  check "allocSlow of two words"
    (replacing (form runtimeAllocSlow [word "bytes", word "kind"] (SPrim Bits64Type) [Word]))
  -- crash (message : ByteAddr) (bytes : Bits64) : Bits64
  check "crash with a result"
    (replacing (form runtimeCrash [parameter "message" Ty.ByteAddr, word "bytes"] (SPrim Bits64Type)
                  [Word]))
  -- the check reads the runtime's forms, the lowering only those it is
  -- given: the runtime has every routine, and a program of no functions,
  -- which calls none, is lowered with none of their forms
  putStrLn ("no routine's form given: " ++ compile standIns [] empty [] [])
  -- prim__exit (status : Int) : PrimIO (), as base declares it
  checkWith "prim__exit as declared" (exitImplementation (SPrim IntType) :: standIns) [exitForeign]
  -- prim__exit (status : Bits64) : PrimIO ()
  checkWith "prim__exit of a Bits64" (exitImplementation (SPrim Bits64Type) :: standIns)
    [exitForeign]
  -- pair = (7, "seven"): its object, and the string's
  checkObjects "a pair and the string it holds"
    (fromList
       [(pairObject, Constructor 1 [Fixnum 7, Object sevenObject]), (sevenObject, Text "seven")])
  checkObjects "a pair without the string it holds"
    (fromList [(pairObject, Constructor 1 [Fixnum 7, Object sevenObject])])
  -- the main expression `length "abc"`, with the routine's form and
  -- without it
  putStrLn ("a string routine in the program, called: " ++ rendered standIns standIns [lengthMain])
  putStrLn ("a string routine outside the program, called: "
            ++ rendered standIns (without utf8Length) [lengthMain])
