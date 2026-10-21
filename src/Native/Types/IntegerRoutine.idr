||| The routines of the bignum encoding's module (`IntegerRoutine`): the
||| operations on an `Integer` beyond the fixnums, which generated code's
||| fast paths leave to the runtime, over values as ordinary code holds them.
|||
||| This module is the contract for them, and the only place it is stated,
||| as `Native.Types.StringRoutine` is for strings: the bignum encoding's
||| module declares the function that is each by its port, and the code
||| generator finds each by that type in that module. The runtime has no
||| such module yet; until it does, a call of one ends the program as
||| `Unsupported` does.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is): it imports nothing from the compiler, so that the runtime's own
||| Idris can import it.
module Native.Types.IntegerRoutine

import Data.List.Elem
import Native.Carrier
import Native.Mach
import Native.Port

%default total

||| The `Integer` routines.
public export
data IntegerRoutine
  = ||| The arithmetic and the bitwise operations of two `Integer`s.
    Add | Sub | Mul | And | Or | Xor | Div | Mod
  | ||| An `Integer` shifted left or right by another.
    Shl | Shr
  | ||| An `Integer` negated.
    Neg
  | ||| The order of two `Integer`s: -1, 0 or 1.
    Compare
  | ||| An `Integer` modulo 2^64, as a word.
    ToBits64
  | ||| The `Integer` of a signed word, and of an unsigned one.
    FromInt64 | FromBits64

||| Whether two `Integer` routines are the same one: how the code generator
||| finds the function that is one.
public export
Eq IntegerRoutine where
  Add == Add = True
  Sub == Sub = True
  Mul == Mul = True
  And == And = True
  Or == Or = True
  Xor == Xor = True
  Div == Div = True
  Mod == Mod = True
  Shl == Shl = True
  Shr == Shr = True
  Neg == Neg = True
  Compare == Compare = True
  ToBits64 == ToBits64 = True
  FromInt64 == FromInt64 = True
  FromBits64 == FromBits64 = True
  _ == _ = False

||| Each `Integer` routine's arrow: what its arguments and its result carry.
public export
port : IntegerRoutine -> Port
port Add =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Sub =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Mul =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port And =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Or = MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Xor =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Div =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Mod =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Shl =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Shr =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Neg = MkPort [Carrier.ValueOf Integer] (Just (Carrier.ValueOf Integer))
port Compare =
  MkPort [Carrier.ValueOf Integer, Carrier.ValueOf Integer] (Just (Carrier.Machine Mach.IWord))
port ToBits64 = MkPort [Carrier.ValueOf Integer] (Just (Carrier.Machine Mach.U64))
port FromInt64 = MkPort [Carrier.Machine Mach.IWord] (Just (Carrier.ValueOf Integer))
port FromBits64 = MkPort [Carrier.Machine Mach.U64] (Just (Carrier.ValueOf Integer))

||| Every `Integer` routine, once, which the code generator pairs with its
||| own copy, element by element.
public export
allIntegerRoutines : List IntegerRoutine
allIntegerRoutines =
  [Add, Sub, Mul, And, Or, Xor, Div, Mod, Shl, Shr, Neg, Compare, ToBits64, FromInt64, FromBits64]

||| The list holds every `Integer` routine.
complete : (r : IntegerRoutine) -> Elem r IntegerRoutine.allIntegerRoutines
complete Add = %search
complete Sub = %search
complete Mul = %search
complete And = %search
complete Or = %search
complete Xor = %search
complete Div = %search
complete Mod = %search
complete Shl = %search
complete Shr = %search
complete Neg = %search
complete Compare = %search
complete ToBits64 = %search
complete FromInt64 = %search
complete FromBits64 = %search
