||| Elaborator reflection, each form reported: the extension, a `%runElab`
||| declaration, and a `%macro` function.
module Reflects

import Language.Reflection

%language ElabReflection

%default total

%macro
answer : Elab Nat
answer = pure 42

%runElab pure ()
