||| The routines of the string encoding's module (`StringRoutine`): the
||| primitive operations on strings and their comparison, over strings as
||| ordinary code holds them, a character its code point, a count or an
||| index a word, an order -1, 0 or 1; and the numbers as text.
|||
||| This module is the contract for them, and the only place it is stated,
||| as `Native.Routine` is for the core's routines: the string encoding's
||| module declares the function that is each by its port, and the code
||| generator finds each by that type in that module.
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is): it imports nothing from the compiler, so that the runtime's own
||| Idris can import it.
module Native.Types.StringRoutine

import Data.List.Elem
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
  _ == _ = False

||| Each string routine's arrow: what its arguments and its result carry.
public export
port : StringRoutine -> Port
port Length = MkPort [Port.ValueOf String] (Just Port.Word)
port Head = MkPort [Port.ValueOf String] (Just Port.Word)
port Tail = MkPort [Port.ValueOf String] (Just (Port.ValueOf String))
port Index = MkPort [Port.ValueOf String, Port.Word] (Just Port.Word)
port Cons = MkPort [Port.Word, Port.ValueOf String] (Just (Port.ValueOf String))
port Append = MkPort [Port.ValueOf String, Port.ValueOf String] (Just (Port.ValueOf String))
port Reverse = MkPort [Port.ValueOf String] (Just (Port.ValueOf String))
port Substr = MkPort [Port.Signed, Port.Signed, Port.ValueOf String] (Just (Port.ValueOf String))
port Compare = MkPort [Port.ValueOf String, Port.ValueOf String] (Just Port.Signed)
port ShowSigned = MkPort [Port.Signed] (Just (Port.ValueOf String))
port ShowUnsigned = MkPort [Port.Word] (Just (Port.ValueOf String))

||| Every string routine, once, which the code generator pairs with its own
||| copy, element by element.
public export
allStringRoutines : List StringRoutine
allStringRoutines = [Length, Head, Tail, Index, Cons, Append, Reverse, Substr, Compare, ShowSigned, ShowUnsigned]

||| The list holds every string routine.
export
complete : (r : StringRoutine) -> Elem r StringRoutine.allStringRoutines
complete Length = Here
complete Head = There (Here)
complete Tail = There (There (Here))
complete Index = There (There (There (Here)))
complete Cons = There (There (There (There (Here))))
complete Append = There (There (There (There (There (Here)))))
complete Reverse = There (There (There (There (There (There (Here))))))
complete Substr = There (There (There (There (There (There (There (Here)))))))
complete Compare = There (There (There (There (There (There (There (There (Here))))))))
complete ShowSigned = There (There (There (There (There (There (There (There (There (Here)))))))))
complete ShowUnsigned = There (There (There (There (There (There (There (There (There (There (Here))))))))))
