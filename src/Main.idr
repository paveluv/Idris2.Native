||| `idris2-native`: Idris 2 with the native code generator, `--cg native`,
||| and the flat oracle, `--cg flat-oracle`, beside its own.
|||
||| Idris makes the first code generator given here the default, so Chez is
||| given first: without `--cg`, `idris2-native` compiles as `idris2` does.
module Main

import Compiler.Common
import Compiler.Native.Native
import Compiler.Scheme.Chez
import Flat.Oracle

import Idris.Driver

main : IO ()
main = mainWithCodegens [ ("chez", codegenChez)
                        , ("native", codegenNative)
                        , ("flat-oracle", codegenFlatOracle) ]
