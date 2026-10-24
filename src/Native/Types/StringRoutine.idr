||| The routines of the string encoding's module (`StringRoutine`): the
||| primitive operations on strings and their comparison, over strings as
||| ordinary code holds them, a character its code point, a count or an
||| index a word, an order -1, 0 or 1; the numbers as text; and a string's
||| text as the system's bytes and back.
|||
||| This module is the contract for them, and the only place it is stated,
||| as `Native.Routine` is for the core's routines: the string encoding's
||| module declares the function that is each by its port, and the code
||| generator finds each by that type in that module. Generated code calls
||| the primitive operations; the runtime's code that speaks to the system
||| calls the text's (`TextBytes` and on), each through an extern declared
||| by its port (`Native.Support.Text`), which the code generator binds to
||| the program's encoding's function, as it binds an OS service's to the
||| platform's. So that code is written once, for every encoding.
|||
||| The system's text is UTF-8, as the system interfaces of every platform
||| targeted take it: paths, the environment, the console, files.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is): it imports nothing from the compiler, so that the runtime's own
||| Idris can import it.
module Native.Types.StringRoutine

import Data.List.Elem
import Native.Carrier
import Native.Field
import Native.Mach
import Native.Port

%default total

||| The string routines.
public export
data StringRoutine
  = Length | Head | Tail | Index | Cons | Append | Reverse
  | ||| The characters from `start`, `len` of them, both clamped to the string.
    Substr
  | Compare
  | ||| A signed word in decimal, as Chez writes it: `-` before a negative
    ||| one's digits.
    ShowSigned
  | ||| A word, unsigned, in decimal.
    ShowUnsigned
  | ||| A double in decimal, as Chez writes it: the shortest digits that read
    ||| back to it.
    ShowDouble
  | ||| The double a string is: the nearest to its decimal, 0.0 where it is
    ||| none.
    ReadDouble
  | ||| The integer a string is, truncated toward zero, modulo 2^64: what each
    ||| cast from a string to an integer type of 64 bits or fewer wraps to its
    ||| width; 0 where it is none.
    ReadWord
  | ||| How many of the system's bytes a string's text takes.
    TextBytes
  | ||| Where a string's own bytes are, if the encoding holds its text as the
    ||| system's bytes: valid until the next allocation; the null address if
    ||| it does not.
    TextAddress
  | ||| A string's text written as the system's bytes at an address, as many
    ||| as `TextBytes` says.
    CopyText
  | ||| A new string of the system's bytes at an address, so many.
    OfText
  | ||| A string walked character by character, by the encoding's own
    ||| positions in it, 0 the first character's: the position after the
    ||| character at a position, the position itself at the end; the
    ||| character at a position before the end; and the string from a
    ||| position on.
    After | CharAt | From

||| Whether two string routines are the same one: how the code generator
||| finds the function that is one.
public export
Eq StringRoutine where
  Length == Length = True
  Head == Head = True
  Tail == Tail = True
  Index == Index = True
  Cons == Cons = True
  Append == Append = True
  Reverse == Reverse = True
  Substr == Substr = True
  Compare == Compare = True
  ShowSigned == ShowSigned = True
  ShowUnsigned == ShowUnsigned = True
  ShowDouble == ShowDouble = True
  ReadDouble == ReadDouble = True
  ReadWord == ReadWord = True
  TextBytes == TextBytes = True
  TextAddress == TextAddress = True
  CopyText == CopyText = True
  OfText == OfText = True
  After == After = True
  CharAt == CharAt = True
  From == From = True
  _ == _ = False

||| Each string routine's arrow: what its arguments and its result carry.
public export
port : StringRoutine -> Port
port Length = "s" ~& String ~> "characters" ~: Mach.U64
port Head = "s" ~& String ~> "character" ~: Mach.U64
port Tail = "s" ~& String ~> "rest" ~& String
port Index = "s" ~& String ~> "i" ~: Mach.U64 ~> "character" ~: Mach.U64
port Cons = "c" ~: Mach.U64 ~> "s" ~& String ~> "cs" ~& String
port Append = "s" ~& String ~> "t" ~& String ~> "st" ~& String
port Reverse = "s" ~& String ~> "reversed" ~& String
port Substr = "start" ~: Mach.IWord ~> "len" ~: Mach.IWord ~> "s" ~& String ~> "part" ~& String
port Compare = "s" ~& String ~> "t" ~& String ~> "order" ~: Mach.IWord
port ShowSigned = "n" ~: Mach.IWord ~> "decimal" ~& String
port ShowUnsigned = "n" ~: Mach.U64 ~> "decimal" ~& String
port ShowDouble = "x" ~: Mach.F64 ~> "decimal" ~& String
port ReadDouble = "decimal" ~& String ~> "x" ~: Mach.F64
port ReadWord = "decimal" ~& String ~> "n" ~: Mach.U64
port TextBytes = "s" ~& String ~> "bytes" ~: Mach.U64
port TextAddress = "s" ~& String ~> "bytes" ~: Carrier.ByteAddr
port CopyText = "s" ~& String ~> "into" ~: Carrier.ByteAddr ~> ()
port OfText = "bytes" ~: Carrier.ByteAddr ~> "count" ~: Mach.U64 ~> "s" ~& String
port After = "s" ~& String ~> "at" ~: Mach.U64 ~> "next" ~: Mach.U64
port CharAt = "s" ~& String ~> "at" ~: Mach.U64 ~> "character" ~: Mach.U64
port From = "s" ~& String ~> "at" ~: Mach.U64 ~> "rest" ~& String

||| Every string routine, once, which the code generator pairs with its own
||| copy, element by element.
public export
allStringRoutines : List StringRoutine
allStringRoutines =
  [ Length, Head, Tail, Index, Cons, Append, Reverse, Substr, Compare, ShowSigned, ShowUnsigned,
    ShowDouble, ReadDouble
  , ReadWord, TextBytes, TextAddress, CopyText, OfText, After, CharAt, From ]

||| The list holds every string routine.
complete : (r : StringRoutine) -> Elem r StringRoutine.allStringRoutines
complete Length = %search
complete Head = %search
complete Tail = %search
complete Index = %search
complete Cons = %search
complete Append = %search
complete Reverse = %search
complete Substr = %search
complete Compare = %search
complete ShowSigned = %search
complete ShowUnsigned = %search
complete ShowDouble = %search
complete ReadDouble = %search
complete ReadWord = %search
complete TextBytes = %search
complete TextAddress = %search
complete CopyText = %search
complete OfText = %search
complete After = %search
complete CharAt = %search
complete From = %search
