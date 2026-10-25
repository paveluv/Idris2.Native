||| What the flat translation reads of Idris's definitions (`Def`), by
||| functions of their own.
|||
||| A match on `TCon`'s fields is made here, not where it is used: inline,
||| in a `do` block, Idris takes seconds to elaborate one (15 s in
||| `Translate.shape`), and a function of its own milliseconds.
module Native.Flat.Definition

import Core.Context.Context
import Core.Name

%default total

||| A type constructor's flags and its data constructors, if the definition
||| is a type constructor whose constructors are known.
export
dataDeclaration : Def -> Maybe (TypeFlags, List Name)
dataDeclaration (TCon _ _ _ flags _ (Just cons) _) = Just (flags, cons)
dataDeclaration _ = Nothing
