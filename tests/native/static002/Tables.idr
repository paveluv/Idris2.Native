-- Constants marked static in a module of their own, which the program
-- `Flat` imports and reads from flat code. A module that imports this one
-- sees its marks: Idris keeps each directive with the module and passes
-- it on to every module that imports it, so the check of a flat function
-- as its module is built (`flat-check`) reads each of these as a constant
-- marked static, as the program's compilation does. This module imports
-- `Squares` too, and does not re-export it, so that `Flat` reaches a mark
-- of a module it does not import (`Squares` says why).
module Tables

import Native.Flat.Uniform
import Native.Types.Bytes
import Squares

%default covering

%cg native static Tables.cubes Tables.limit Tables.step Tables.ratio Tables.huge
%cg native static Tables.small Tables.unit Tables.flag

-- Words a maker made, as if written
--
--   cubes = <a BYTES object: its header, then the words 0, 1, 8, ..., 343>
--
-- one object in the image's read-only data.
export
cubes : Bytes
cubes = generate 8 (\i => cast (i * i * i))

-- As if written `limit = 9223372036854775815`: a word whose top two bits
-- differ, which ordinary code would hold as an `INT64` box, and flat code
-- holds as the word it is.
export
limit : Bits64
limit = 0x8000000000000000 + 7

-- As if written `step = 42`.
export
step : Int
step = 6 * 7

-- As if written `ratio = 0.25`.
export
ratio : Double
ratio = 1.0 / 4.0

-- As if written `huge = MkUniform 1180591620717411303424`, 2^70, outside
-- the fixnum range: an `Integer` as ordinary code holds it, a `BIGNUM` in
-- the image, which flat code holds as its address.
export
huge : Uniform Integer
huge = MkUniform (2 * 0x200000000000000000)

-- As if written `small = MkUniform 15`: an `Integer` in the fixnum range,
-- which ordinary code holds as the fixnum, and flat code too.
export
small : Uniform Integer
small = MkUniform (3 * 5)

-- As if written `unit = MkUniform ()`: `()`, which Idris erases, is the
-- erased value, which flat code holds as its word, as ordinary code does.
export
unit : Uniform ()
unit = MkUniform ()

-- As if written `flag = True`. Idris compiles a type whose constructors
-- have no fields, as `Bool`'s, to the numbers of its constructors, so
-- ordinary code holds `flag` as the fixnum 1. Flat code holds a `Bool` as
-- its tag, a data type's layout, which is neither one uniform value nor a
-- machine scalar, so a flat read of `flag` is not its value: it calls the
-- constant's flat form, which computes it. Ordinary code reads its value,
-- with no call.
export
flag : Bool
flag = 2 < 3

-- Word `i` of the squares of the module `Squares`: an ordinary function,
-- which a flat function that calls it reaches.
export
square : Int -> Bits64
square i = uncheckedWord squares i 0
