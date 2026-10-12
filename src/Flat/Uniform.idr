||| A value held as the ordinary regime holds it, for flat code.
|||
||| A flat function holds its values in registers, a word or a double each,
||| and a type whose values do not fit is not flat. `Uniform a` is the way
||| across, written where it is wanted: a flat function may take or return a
||| `Uniform a` for any `a`, flat or not, and holds it in one register as
||| ordinary code holds a value of `a`, whatever that is for the code
||| generator. Flat code does not look inside: it passes the value on,
||| stores it, or hands it to a primitive that knows how ordinary code lays
||| out an `a`. Of a flat type, `Uniform a` is that type as ordinary code
||| holds it, opaque until opened, as `Uniform Bits64` is a fixnum or a box
||| to the native code generator.
|||
||| A record of one field, so ordinary code holds a `Uniform a` as an `a`:
||| crossing costs nothing at the boundary. The module imports nothing of the
||| compiler, so that any program, and the native runtime, may import it.
module Flat.Uniform

%default total

public export
record Uniform a where
  constructor MkUniform
  value : a
