-- A module of the group of the type layer, `Native.Types`, written for
-- this test: the code generator checks the makers it defines as it checks
-- the group's own, when it compiles any program that imports it.
--
-- A `Fake` is a record of one field, a `Bytes`, which Idris erases, so a
-- `Fake` is held as its `Bytes`, a `BYTES` object no one writes, which
-- the statements below say.
module Native.Types.Fake

import Native.Types.Bytes
import Native.Types.FromWords
import Native.Types.Kind
import Native.Types.Repr

%default total

export
record Fake where
  constructor MkFake
  bytes : Bytes

public export
Only Kind.BYTES Fake where

public export
Immutable Fake where

-- A maker of a `Fake`, in the module that defines `Fake`, but marked
-- `%inline`: Idris puts its body, `MkFake (generate n f)`, in place of
-- each call, so no call of it is left for the evaluation to take for the
-- object of its words.
public export %inline
fake : FromWords Fake
fake n f = MkFake (generate n f)

-- A maker of a `Bytes` outside the module that defines `Bytes`, which
-- answers for what its makers say.
export
misplaced : FromWords Bytes
misplaced n f = generate n f
