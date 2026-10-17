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
||| The contract itself is shared, `Native.Port` and its entries
||| (`Native.Routines`, `Native.Intrinsic`, `Native.Service`): each side
||| gives what it provides checked by Idris against the ports where that
||| side is built, and the code generator takes the registers of each call
||| from the ports, and the function or extern of each entry by its type (an
||| inline extern, a service) or from the record of them (a routine). A routine the runtime gives must also have a
||| flat form, which the lowering checks. Code compiled to join a runtime
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
  ||| The function of the runtime library that is the routine; for one the
  ||| runtime does not have yet, the name its calls use.
  name : Name
  ||| Whether the runtime has it. A call of a routine it does not have ends
  ||| the program as `Unsupported` does.
  provided : Bool
  ||| The symbol by which the rendering and the seed reach it, if they do:
  ||| the rendering defines it at the routine's function.
  symbol : Maybe Sym
  results : List (IRCommon.Ty enc)
  params : List (IRCommon.Ty enc)

||| The register a carrier of the contract is in: a word, a signed word or
||| an address in a word, a value as ordinary code holds it in a uniform
||| register.
public export
carrierTy : Port.Carrier -> IRCommon.Ty enc
carrierTy Port.Word = IRCommon.Ty.W64
carrierTy Port.Signed = IRCommon.Ty.W64
carrierTy Port.Address = IRCommon.Ty.W64
carrierTy Port.Raw = IRCommon.Ty.W64
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

||| The routine for an `Integer` operation the fast paths leave to the
||| runtime, which has none yet.
public export
integerRoutine : String -> Name
integerRoutine op = UN (Basic ("idris_integer_" ++ op))

||| The name of a string routine the runtime has no module for, under the
||| encoding: a call of one ends the program as `Unsupported` does.
stubName : Types.StringRoutine -> Name
stubName c = UN (Basic ("idris_string_" ++ op c))
  where
    op : Types.StringRoutine -> String
    op Types.StringRoutine.Length = "length"
    op Types.StringRoutine.Head = "head"
    op Types.StringRoutine.Tail = "tail"
    op Types.StringRoutine.Index = "index"
    op Types.StringRoutine.Cons = "cons"
    op Types.StringRoutine.Append = "append"
    op Types.StringRoutine.Reverse = "reverse"
    op Types.StringRoutine.Substr = "substr"
    op Types.StringRoutine.Compare = "compare"
    op Types.StringRoutine.ShowSigned = "show_signed"
    op Types.StringRoutine.ShowUnsigned = "show_unsigned"

||| The name generated code calls a string routine by.
export
stringRoutine : Realised -> Types.StringRoutine -> Name
stringRoutine r c = case r.strings of
  Just ss => maybe (stubName c) (flatName . fst) (find ((== c) . snd) ss)
  Nothing => stubName c

||| The routines, with their registers: the generic runtime's and the string
||| encoding's as the loaded runtime realises them, and the `Integer`
||| operations, which the runtime has none of yet.
export
routines : {enc : Types.Enc} -> Realised -> List (RoutineCall enc)
routines r =
  map generic r.routines
    ++ strings
    ++ [ integer "add" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "sub" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "mul" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "and" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "or" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "xor" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "div" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "mod" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "shl" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "shr" [IRCommon.Ty.Val] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "neg" [IRCommon.Ty.Val] [IRCommon.Ty.Val]
       , integer "compare" [IRCommon.Ty.W64] [IRCommon.Ty.Val, IRCommon.Ty.Val]
       , integer "to_bits64" [IRCommon.Ty.W64] [IRCommon.Ty.Val]
       , integer "from_int64" [IRCommon.Ty.Val] [IRCommon.Ty.W64]
       , integer "from_bits64" [IRCommon.Ty.Val] [IRCommon.Ty.W64] ]
  where
    ||| The symbol the rendering and the seed reach a routine of the core by.
    symbolOf : Routine -> Sym
    symbolOf Routine.Start = Sym.SymRuntimeStart
    symbolOf Routine.AllocSlow = Sym.SymAllocSlow
    symbolOf Routine.AllocMutable = Sym.SymAllocMutable
    symbolOf Routine.Crash = Sym.SymCrash

    generic : (Name, Routine) -> RoutineCall enc
    generic (n, c) = MkRoutineCall n True (Just (symbolOf c)) (portResults (Routine.port c)) (portParams (Routine.port c))

    provided : (Name, Types.StringRoutine) -> RoutineCall enc
    provided (n, c) =
      MkRoutineCall n True Nothing (portResults (Types.StringRoutine.port c)) (portParams (Types.StringRoutine.port c))

    stub : Types.StringRoutine -> RoutineCall enc
    stub c = MkRoutineCall (stubName c) False Nothing (portResults (Types.StringRoutine.port c)) (portParams (Types.StringRoutine.port c))

    strings : List (RoutineCall enc)
    strings = case r.strings of
      Just ss => map provided ss
      Nothing => map stub Types.StringRoutine.allStringRoutines

    integer : String -> List (IRCommon.Ty enc) -> List (IRCommon.Ty enc) -> RoutineCall enc
    integer op rs ps = MkRoutineCall (integerRoutine op) False Nothing rs ps

||| The symbol the routine whose function has the name is reached by.
export
routineSymbol : {enc : Types.Enc} -> Realised -> Name -> Maybe Sym
routineSymbol r n = do
  x <- find (\x => x.provided && flatName x.name == n) (routines {enc} r)
  x.symbol
