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
import Native.Field
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
  | ||| An `Integer` in decimal, `-` before a negative one's digits, and the
    ||| `Integer` a string is, as the integer types read one, unwrapped: a
    ||| sign, digits with at most one point, truncated toward zero; 0 where it
    ||| is none.
    ToDecimal | FromDecimal
  | ||| The double nearest an `Integer`, ties to even, an infinity beyond the
    ||| largest; and a double's `Integer`, its exact truncation, 0 for NaN and
    ||| the infinities.
    ToDouble | FromDouble

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
  ToDecimal == ToDecimal = True
  FromDecimal == FromDecimal = True
  ToDouble == ToDouble = True
  FromDouble == FromDouble = True
  _ == _ = False

||| Each `Integer` routine's arrow: what its arguments and its result carry.
public export
port : IntegerRoutine -> Port
port Add = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Sub = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Mul = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port And = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Or = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Xor = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Div = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Mod = "x" ~& Integer ~> "y" ~& Integer ~> "result" ~& Integer
port Shl = "x" ~& Integer ~> "count" ~& Integer ~> "result" ~& Integer
port Shr = "x" ~& Integer ~> "count" ~& Integer ~> "result" ~& Integer
port Neg = "x" ~& Integer ~> "result" ~& Integer
port Compare = "x" ~& Integer ~> "y" ~& Integer ~> "order" ~: Mach.IWord
port ToBits64 = "x" ~& Integer ~> "word" ~: Mach.U64
port FromInt64 = "word" ~: Mach.IWord ~> "x" ~& Integer
port FromBits64 = "word" ~: Mach.U64 ~> "x" ~& Integer
port ToDecimal = "x" ~& Integer ~> "decimal" ~& String
port FromDecimal = "decimal" ~& String ~> "x" ~& Integer
port ToDouble = "x" ~& Integer ~> "nearest" ~: Mach.F64
port FromDouble = "x" ~: Mach.F64 ~> "truncated" ~& Integer

||| Every `Integer` routine, once, which the code generator pairs with its
||| own copy, element by element.
public export
allIntegerRoutines : List IntegerRoutine
allIntegerRoutines =
  [ Add, Sub, Mul, And, Or, Xor, Div, Mod, Shl, Shr, Neg, Compare, ToBits64, FromInt64, FromBits64
  , ToDecimal, FromDecimal, ToDouble, FromDouble ]

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
complete ToDecimal = %search
complete FromDecimal = %search
complete ToDouble = %search
complete FromDouble = %search
