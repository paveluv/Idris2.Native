||| The shape of an entry of the contract (`Port`): what each register of a
||| call across it carries, as data. The runtime gives it an Idris type
||| (`Native.Runtime.PortTy`).
|||
||| The contract's entries are the runtime's routines, which generated code
||| calls, the inline externs, which the lowering provides to the runtime's
||| code, and the OS services, which a platform provides to the rest of the
||| runtime; and the routines of the string and bignum encodings' modules.
||| Each kind of entry is an enumeration whose `port` gives each entry's
||| arrow, the one place its shape is stated (`Native.Routine`,
||| `Native.Intrinsic`, `Native.Service`, `Native.Types.StringRoutine`,
||| `Native.Types.IntegerRoutine`), written as an arrow from what the entry
||| takes to what it gives (`~>`). The side that provides an entry declares
||| it by its port's Idris type, which Idris checks where it is defined; the
||| code generator finds it by that type, checks there is one of each, and
||| reads the registers of a call from the port, the same data. Neither
||| restates the other.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Port

-- lint: allow public-import: a port is written with the named carriers'
-- operators (`~:`, `~&`, `~*`), and reduces through their fields, which every
-- module that writes or reads one needs
import public Native.Field

import Native.Carrier

%default total

||| An entry's shape: what its arguments carry, in order, and what its
||| result does, if it has one. Every entry takes the token too, last, and
||| returns it with the result: it is an operation (`Op`).
public export
record Port where
  constructor MkPort
  takes : List Carrier
  gives : Maybe Carrier

||| What may stand right of a port's arrow: the rest of the port, what the
||| entry gives, a named carrier (`Native.Field`), or `()`, for an entry
||| that gives nothing, as its Idris type then returns `()`.
public export
interface Rest a where
  rest : a -> Port

public export
Rest Port where
  rest p = p

public export
Rest Field where
  rest f = MkPort [] (Just f.carrier)

public export
Rest () where
  rest () = MkPort [] Nothing

||| What may stand left of a port's arrow: a named carrier the entry takes,
||| or `()`, for an entry that takes nothing.
public export
interface Takes a where
  carriers : a -> List Carrier

public export
Takes Field where
  carriers f = [f.carrier]

public export
Takes () where
  carriers () = []

export infixr 1 ~>

||| A port, written as the arrow of its entry's Idris type is, one argument
||| at a time, each register named as a record's field is (`Native.Field`):
||| `"handle" ~: Mach.U64 ~> "bytes" ~: Carrier.ByteAddr ~> "count" ~: Mach.U64
||| ~> "written" ~: Mach.U64` takes a word, a byte address and a word and
||| gives a word; `() ~> ()` takes and gives nothing. The names are erased,
||| the port's structured comments: a port is its carriers alone.
public export
(~>) : Takes a => Rest b => a -> b -> Port
x ~> y = MkPort (carriers x ++ (rest y).takes) (rest y).gives
