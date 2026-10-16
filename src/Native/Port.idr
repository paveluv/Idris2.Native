||| The shape of an entry of the contract (`Port`): what each register of a
||| call across it carries, as data. The runtime gives it an Idris type
||| (`Native.Runtime.PortTy`).
|||
||| The contract's entries are the runtime's routines, which generated code
||| calls, the inline externs, which the lowering provides to the runtime's
||| code, and the OS services, which a platform provides to the rest of the
||| runtime (`Native.Routines`, `Native.Intrinsic`, `Native.Services`). Each
||| has a port, the one place its shape is stated: the side that provides an
||| entry gives a value of the port's Idris type, which Idris checks where
||| that side is built; the code generator reads the registers of a call
||| from the port, the same data. Neither restates the other. The inline
||| externs are keyed by an enumeration (`Native.Intrinsic`); the others are
||| still fields of a record whose type is their port.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Port


%default total

||| What a register carries across the boundary, as the Idris type it is.
public export
data Carrier
  = ||| A word: `Bits64`.
    Word
  | ||| A signed word: `Int`.
    Signed
  | ||| A value of the type, as ordinary code holds it: `Uniform t`.
    ValueOf Type
  | ||| Any value, as ordinary code holds it: `Uniform a`, for the call's `a`.
    Value
  | ||| The address of an object of the call's shape `s`, as the side that
    ||| gives the entry types addresses: `addr s`.
    Address

||| An entry's shape: what its arguments carry, in order, and what its
||| result does, if it has one. Every entry takes the token too, last, and
||| returns it with the result: it is an operation (`Op`).
public export
record Port where
  constructor MkPort
  takes : List Carrier
  gives : Maybe Carrier
