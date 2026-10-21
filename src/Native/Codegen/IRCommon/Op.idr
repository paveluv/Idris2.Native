||| The operations of the IRs: on integers (`ArithOp`, `UnOp`), on doubles
||| (`FOp`), between the two (`ConvOp`), the comparison relations (`Rel`),
||| and the narrow widths of loads, stores and extensions (`SubWord`).
|||
||| Part of the vocabulary the native backend's two IRs share
||| (`Native.Codegen.IRCommon.Ty` says what it is).
module Native.Codegen.IRCommon.Op

%default total

||| Integer operations, on `W64`s or on `Fix`es (`Arith`). A shift takes its
||| count as the second operand, below the word's width; `Shr` is logical and
||| `Sar` arithmetic. The divisions truncate toward zero; dividing by zero, or
||| the most negative word by −1 with `DivS` or `RemS`, is undefined, so the
||| producer checks for both first.
public export
data ArithOp = Add | Sub | Mul | And | Or | Xor | Shl | Shr | Sar
             | DivS | DivU | RemS | RemU

public export
Show ArithOp where
  show Add = "Add"
  show Sub = "Sub"
  show Mul = "Mul"
  show And = "And"
  show Or = "Or"
  show Xor = "Xor"
  show Shl = "Shl"
  show Shr = "Shr"
  show Sar = "Sar"
  show DivS = "DivS"
  show DivU = "DivU"
  show RemS = "RemS"
  show RemU = "RemU"

||| Conversions between raw integers and doubles.
public export
data ConvOp
  = ||| A signed `W64` to the `F64` of its value.
    I2F
  | ||| An `F64` to a `W64`, truncated toward zero.
    F2I
  | ||| An `F64`'s 64 bits, reinterpreted as a `W64`.
    FBits
  | ||| A `W64`'s 64 bits, reinterpreted as an `F64`.
    BitsF

||| Double arithmetic.
public export
data FOp = FAdd | FSub | FMul | FDiv

public export
Show FOp where
  show FAdd = "FAdd"
  show FSub = "FSub"
  show FMul = "FMul"
  show FDiv = "FDiv"

||| Comparison relations on integers; `S` and `U` are signed and unsigned. On
||| `Fix`es a relation compares the fixnums' values, as 64-bit integers; every
||| value encoding with fixnums orders the words as it orders the values, both
||| signed and unsigned, so a rendering compares the words.
public export
data Rel = EqR | NeR | LtS | LeS | GtS | GeS | LtU | LeU | GtU | GeU

||| `Negate` is two's-complement negation; `Complement` flips every bit.
public export
data UnOp = Negate | Complement
