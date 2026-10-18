-- The layout of each argument and of the result of a flat function: the
-- registers its values take, by its type, which the dump of the forms
-- shows. A register is a machine word or a double. The generic function has
-- forms at static arguments only, so none.

-- A token: one constructor and no fields, so no registers.
record Ordo where
  constructor MkOrdo

-- A record takes its fields' registers in turn: a word for `count`, a
-- double for `scale`, none for `token`, and a word for `flag`, whose
-- constructor's tag is its value.
record Mixed where
  constructor MkMixed
  count : Bits8
  scale : Double
  token : Ordo
  flag : Bool

-- A word for the constructor's tag, then each constructor's fields in turn,
-- sharing no register: `Circle`'s double, `Rect`'s two words, and nothing
-- for `Empty`. Four registers, of which a value uses those of its own
-- constructor.
data Shape = Circle Double | Rect Bits64 Bits64 | Empty

-- A machine integer and a `Char` take a word each.
%cg native flat Main.word
word : Bits64 -> Char
word _ = 'a'

-- A double takes a double register, and the token result none.
%cg native flat Main.double
double : Double -> Ordo
double _ = MkOrdo

-- As if written with the registers as arguments and results:
-- `Bits8 -> Double -> Bool -> (Bits64, Bits64, Bits64)`, the triple three
-- words.
%cg native flat Main.mixed
mixed : Mixed -> (Bits64, Bits64, Bits64)
mixed _ = (1, 2, 3)

-- A tag and `Just`'s double.
%cg native flat Main.enum
enum : Bool -> Maybe Double
enum _ = Nothing

-- `()`, one constructor and no fields, takes no register.
%cg native flat Main.shape
shape : Shape -> ()
shape _ = ()

-- A type made of the function's erased arguments is deferred: the registers
-- of an `a` are known only where `deferred` is called at some `a`, so each
-- call from flat code gets a copy, as if `deferred` had been written at that
-- type, such as `deferredDouble : Double -> Bits64`.
%cg native flat Main.deferred
deferred : {0 a : Type} -> a -> Bits64
deferred _ = 0

main : IO ()
main = pure ()
