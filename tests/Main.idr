||| The tests of `idris2-native`, by Idris's golden test runner: each test is
||| a directory whose `run` script's output must be its `expected`.
module Main

import Test.Golden

%default covering

nativeTests : IO TestPool
nativeTests = testsInDir "native" "The native code generator"

flatTests : IO TestPool
flatTests = testsInDir "flat" "Flat functions"

main : IO ()
main = runner !(sequence [nativeTests, flatTests])
