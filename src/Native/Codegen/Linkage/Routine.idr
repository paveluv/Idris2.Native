||| The routines of the runtime that generated code reaches, as their calls
||| do (`RoutineCall`): with their registers.
|||
||| The modules of `Native.Codegen.Linkage` are the code generator's side of
||| what generated code, the runtime and the linker agree on: the contract as
||| the loaded runtime realises it (`Realised`), the instructions of the
||| inline externs (`Expansion`), the routines here, the foreign
||| functions the runtime implements (`ForeignFunctions`), where a
||| platform's services are (`OSService`), where the runtime's modules are
||| (`RuntimeModule`), the image's symbols and their labels (`Sym`), the
||| sizes of the per-thread areas (`Areas`), and the shape of a resume point
||| (`ResumePoint`). Nothing here is code: the runtime's routines are the
||| runtime library's, the rest of the seed's are `Native.Codegen.Seed`, and
||| `Native.Codegen.Link` makes the image.
|||
||| The contract itself is shared, `Native.Port` and the enumerations of its
||| entries (`Native.Port` says what they are): each side declares what it
||| provides by the ports, which Idris checks where it is defined, and the
||| code generator finds the function or extern of each entry by its type
||| (`Realised`) and takes the registers of each call from the port. A
||| routine the runtime gives must also have a flat form, which the lowering
||| checks. Code compiled to join a runtime
||| that is already built depends on the contract alone.
module Native.Codegen.Linkage.Routine

import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Sym

import Core.Name
import Core.Name.Namespace
import Data.List
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Port
import Native.Routine
import Native.Types.Enc as Types
import Native.Types.IntegerRoutine as Types
import Native.Types.StringRoutine as Types

%default total

||| The name of the `Direct` function of a flat form, which a form's
||| function has: the name by which generated code calls a routine of the
||| runtime.
public export
flatName : Name -> Name
flatName n = NS (mkNamespace "_flat") n

||| A routine of the runtime that generated code reaches, as its calls do:
||| the function, its symbol and its registers.
public export
record RoutineCall (enc : Types.Enc) where
  constructor MkRoutineCall
  ||| The function of the runtime library that is the routine.
  name : Name
  ||| The symbol by which the rendering and the seed reach it, if they do:
  ||| the rendering defines it at the routine's function.
  symbol : Maybe Sym
  results : List (IRCommon.Ty enc)
  params : List (IRCommon.Ty enc)

||| The register a carrier of the contract is in: a word, a signed word or
||| an address in a word, a double in a double's, a value as ordinary code
||| holds it in a uniform register.
public export
carrierTy : Port.Carrier -> IRCommon.Ty enc
carrierTy Port.Word = IRCommon.Ty.W64
carrierTy Port.Signed = IRCommon.Ty.W64
carrierTy Port.Dbl = IRCommon.Ty.F64
carrierTy Port.Address = IRCommon.Ty.W64
carrierTy Port.ByteAddr = IRCommon.Ty.W64
carrierTy (Port.ValueOf _) = IRCommon.Ty.Val
carrierTy Port.Value = IRCommon.Ty.Val

||| The registers of a call of a port's entry: its arguments', the token
||| taking none.
public export
portParams : Port -> List (IRCommon.Ty enc)
portParams p = map carrierTy p.takes

||| The registers of a port's result: none, or its carrier's.
public export
portResults : Port -> List (IRCommon.Ty enc)
portResults p = maybe [] (\c => [carrierTy c]) p.gives

||| The name generated code calls a string routine by, if the runtime has a
||| module for the program's string encoding.
export
stringRoutine : Realised -> Types.StringRoutine -> Maybe Name
stringRoutine r c = do
  ss <- r.strings
  (n, _) <- find ((== c) . snd) ss
  pure (flatName n)

||| The name generated code calls an `Integer` routine by, if the runtime has
||| a module for the program's bignum encoding.
export
integerRoutine : Realised -> Types.IntegerRoutine -> Maybe Name
integerRoutine r c = do
  is <- r.integers
  (n, _) <- find ((== c) . snd) is
  pure (flatName n)

||| The routines, with their registers: the generic runtime's, the string
||| encoding's and the bignum encoding's, as the loaded runtime realises
||| them; none of an encoding it has no module for, whose calls end the
||| program as `Unsupported` does.
export
routines : {enc : Types.Enc} -> Realised -> List (RoutineCall enc)
routines r =
  map generic r.routines
    ++ strings
    ++ integers
  where
    ||| The symbol the rendering and the seed reach a routine of the core by.
    symbolOf : Routine -> Sym
    symbolOf Routine.Start = Sym.SymRuntimeStart
    symbolOf Routine.AllocSlow = Sym.SymAllocSlow
    symbolOf Routine.AllocMutable = Sym.SymAllocMutable
    symbolOf Routine.Crash = Sym.SymCrash

    generic : (Name, Routine) -> RoutineCall enc
    generic (n, c) =
      MkRoutineCall n (Just (symbolOf c)) (portResults (Routine.port c))
        (portParams (Routine.port c))

    string : (Name, Types.StringRoutine) -> RoutineCall enc
    string (n, c) =
      MkRoutineCall n Nothing (portResults (Types.StringRoutine.port c))
        (portParams (Types.StringRoutine.port c))

    integer : (Name, Types.IntegerRoutine) -> RoutineCall enc
    integer (n, c) =
      MkRoutineCall n Nothing (portResults (Types.IntegerRoutine.port c))
        (portParams (Types.IntegerRoutine.port c))

    strings : List (RoutineCall enc)
    strings = maybe [] (map string) r.strings

    integers : List (RoutineCall enc)
    integers = maybe [] (map integer) r.integers

||| The symbol the routine whose function has the name is reached by.
export
routineSymbol : {enc : Types.Enc} -> Realised -> Name -> Maybe Sym
routineSymbol r n = do
  x <- find (\x => flatName x.name == n) (routines {enc} r)
  x.symbol
