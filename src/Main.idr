||| `idris2-native`: Idris 2 with the native code generator, `--cg native`,
||| and the flat oracle, `--cg flat-oracle`, beside its own.
|||
||| Idris makes the first code generator given here the default, so Chez is
||| given first: without `--cg`, `idris2-native` compiles as `idris2` does.
|||
||| `flat-check` compiles nothing: as an incremental code generator it checks
||| each module's flat functions as the module is built (`Flat.Check`). `idris2-native` adds it to the
||| incremental code generators Idris reads from `IDRIS2_INC_CGS`, so a
||| function that is not flat is reported when its module is checked, with
||| the location of the term at fault.
module Main

import Compiler.Common
import Compiler.Native.Native
import Compiler.Scheme.Chez
import Flat.Check
import Flat.Oracle

import Data.List1
import Data.String

import Idris.Driver

import System

||| The incremental code generators the environment names, and `flat-check`.
incremental : Maybe String -> String
incremental Nothing = "flat-check"
incremental (Just cgs)
    = if "flat-check" `elem` map trim (forget (split (== ',') cgs)) then cgs else cgs ++ ",flat-check"

main : IO ()
main = do
  cgs <- getEnv "IDRIS2_INC_CGS"
  ignore (setEnv "IDRIS2_INC_CGS" (incremental cgs) True)
  mainWithCodegens [ ("chez", codegenChez)
                   , ("native", codegenNative)
                   , ("flat-oracle", codegenFlatOracle)
                   , ("flat-check", codegenFlatCheck) ]
