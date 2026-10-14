||| The routines of the runtime that generated code reaches (`Routine`).
|||
||| The modules of `Compiler.Native.Linkage` are what generated code, the
||| runtime and the linker agree on: the runtime contract (its routines here,
||| `InlineExtern`, `ForeignFunctions` and `OSService`), the image's symbols and
||| their labels (`Sym`), the per-thread memory areas (`Areas`), and the
||| shape of a resume point (`ResumePoint`). Nothing here is code: the
||| runtime's routines are the runtime library's, the rest of the seed's are
||| `Compiler.Native.Seed`, and `Compiler.Native.Link` makes the image.
|||
||| What generated code and the runtime may assume of each other is declared
||| here, not taken from the runtime's compilation, in both directions. The
||| routines are what the runtime provides: each reached by name or by
||| symbol, with its signature in the term IR; the lowering calls them as
||| declared, and the runtime library's flat forms are checked against the
||| declarations when a program is lowered. The inline externs are what the
||| lowering provides to fragment code: `%extern` declarations of the runtime
||| library that the flat lowering turns into instructions; each is checked
||| against its declaration when the runtime is loaded. A routine or an
||| inline extern that is missing or has another signature is an error of the
||| compilation. The OS services are what an operating system provides to
||| the rest of the runtime: `%extern` declarations of the generic runtime,
||| each bound, for the platform a program is compiled for, to a function of
||| that platform's module, which the flat lowering calls in its place; the
||| declarations are checked when the runtime is loaded, and the functions
||| when a program is lowered. Code compiled to join a runtime that is
||| already built depends on the contract alone.
module Compiler.Native.Linkage.Routine

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.StringEnc
import Compiler.Native.IRCommon.Ty
import Compiler.Native.Linkage.Sym
import Core.Name
import Core.Name.Namespace
import Data.List

%default total

||| The name of the `Direct` function of a flat form, which a form's
||| function has: the name by which generated code calls a routine of the
||| runtime.
public export
flatName : Name -> Name
flatName n = NS (mkNamespace "_flat") n

||| A routine of the runtime that generated code reaches.
public export
record Routine (enc : Enc) where
  constructor MkRoutine
  ||| The function of the runtime library that is the routine; for one the
  ||| runtime does not have yet, the name its calls use.
  name : Name
  ||| Whether the runtime has it. A call of a routine it does not have ends
  ||| the program as `Unsupported` does.
  provided : Bool
  ||| The symbol by which the rendering and the seed reach it, if they do:
  ||| the rendering defines it at the routine's function.
  symbol : Maybe Sym
  results : List (Ty enc)
  params : List (Ty enc)

||| The routine that starts the program, before `main`: the stack limit, the
||| first allocation window, the arguments.
public export
runtimeStart : Name
runtimeStart = NS (mkNamespace "Runtime.Start") (UN (Basic "start"))

||| The allocation slow path: `bytes` in, the space of an object out, with
||| the window moved past it; it collects when the heap has grown enough.
public export
runtimeAllocSlow : Name
runtimeAllocSlow = NS (mkNamespace "Runtime.Space") (UN (Basic "allocSlow"))

||| The allocation of a mutable object, which is never inline: `bytes` in,
||| the object's space out.
public export
runtimeAllocMutable : Name
runtimeAllocMutable = NS (mkNamespace "Runtime.Space") (UN (Basic "allocMutable"))

||| The routine that writes a message to the standard error and ends the
||| process with status 1.
public export
runtimeCrash : Name
runtimeCrash = NS (mkNamespace "Runtime.System") (UN (Basic "crash"))

||| The routine for an `Integer` operation the fast paths leave to the
||| runtime, which has none yet.
public export
integerRoutine : String -> Name
integerRoutine op = UN (Basic ("idris_integer_" ++ op))

||| The runtime's module that lays strings out under the encoding: the one
||| module of the runtime that reads a string's header or bytes. Every other
||| part of the runtime asks it. None yet for UTF-32.
export
stringModule : StringEnc -> Maybe Namespace
stringModule Utf8 = Just (mkNamespace "Runtime.String.Utf8")
stringModule Utf32 = Nothing

||| A string routine under the encoding: the string module's function of the
||| operation's name, and whether the runtime has it.
stringFunction : StringEnc -> String -> (Name, Bool)
stringFunction e op = case stringModule e of
  Just ns => (NS ns (UN (Basic op)), True)
  Nothing => (UN (Basic ("idris_string_" ++ op)), False)

||| The name generated code calls a string routine by.
export
stringRoutine : Enc -> String -> Name
stringRoutine enc op = case stringFunction enc.string op of
  (n, True) => flatName n
  (n, False) => n

||| The routines, with their signatures. The string routines are the eight
||| primitive operations on strings and their comparison (-1, 0 or 1), over
||| strings as ordinary code holds them; a character is its code point, a
||| count or an index a word.
export
routines : {enc : Enc} -> List (Routine enc)
routines =
  [ string "length" [W64] [Val]
  , string "head" [W64] [Val]
  , string "tail" [Val] [Val]
  , string "index" [W64] [Val, W64]
  , string "cons" [Val] [W64, Val]
  , string "append" [Val] [Val, Val]
  , string "reverse" [Val] [Val]
  , string "substr" [Val] [W64, W64, Val]
  , string "compare" [W64] [Val, Val]
  , MkRoutine runtimeStart True (Just SymRuntimeStart) [] [W64, W64]
  , MkRoutine runtimeAllocSlow True (Just SymAllocSlow) [W64] [W64]
  , MkRoutine runtimeAllocMutable True (Just SymAllocMutable) [W64] [W64]
  , MkRoutine runtimeCrash True (Just SymCrash) [] [W64, W64]
  , integer "add" [Val] [Val, Val]
  , integer "sub" [Val] [Val, Val]
  , integer "mul" [Val] [Val, Val]
  , integer "and" [Val] [Val, Val]
  , integer "or" [Val] [Val, Val]
  , integer "xor" [Val] [Val, Val]
  , integer "div" [Val] [Val, Val]
  , integer "mod" [Val] [Val, Val]
  , integer "shl" [Val] [Val, Val]
  , integer "shr" [Val] [Val, Val]
  , integer "neg" [Val] [Val]
  , integer "compare" [W64] [Val, Val]
  , integer "to_bits64" [W64] [Val]
  , integer "from_int64" [Val] [W64]
  , integer "from_bits64" [Val] [W64] ]
  where
    integer : String -> List (Ty enc) -> List (Ty enc) -> Routine enc
    integer op rs ps = MkRoutine (integerRoutine op) False Nothing rs ps

    string : String -> List (Ty enc) -> List (Ty enc) -> Routine enc
    string op rs ps = let (n, p) = stringFunction enc.string op in MkRoutine n p Nothing rs ps

||| The symbol the routine whose function has the name is reached by.
export
routineSymbol : {enc : Enc} -> Name -> Maybe Sym
routineSymbol n = do
  r <- find (\r => r.provided && flatName r.name == n) (routines {enc})
  r.symbol
