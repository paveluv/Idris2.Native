||| `StringRoutines`, from `Native.Routines`.
module Native.Types.StringRoutines

import Native.Port

%default total

||| The primitive operations on strings and their comparison, over strings
||| as ordinary code holds them: a character is its code point, a count or
||| an index a word, an order -1, 0 or 1; and the numbers as text.
public export
record StringRoutines (f : Port -> Type) where
  constructor MkStringRoutines
  length : f (MkPort [Port.ValueOf String] (Just Port.Word))
  head : f (MkPort [Port.ValueOf String] (Just Port.Word))
  tail : f (MkPort [Port.ValueOf String] (Just (Port.ValueOf String)))
  index : f (MkPort [Port.ValueOf String, Port.Word] (Just Port.Word))
  cons : f (MkPort [Port.Word, Port.ValueOf String] (Just (Port.ValueOf String)))
  append : f (MkPort [Port.ValueOf String, Port.ValueOf String] (Just (Port.ValueOf String)))
  reverse : f (MkPort [Port.ValueOf String] (Just (Port.ValueOf String)))
  ||| The characters from `start`, `len` of them, both clamped to the string.
  substr : f (MkPort [Port.Signed, Port.Signed, Port.ValueOf String] (Just (Port.ValueOf String)))
  compare : f (MkPort [Port.ValueOf String, Port.ValueOf String] (Just Port.Signed))
  ||| A signed word in decimal, as Chez writes it: `-` before a negative
  ||| one's digits.
  showSigned : f (MkPort [Port.Signed] (Just (Port.ValueOf String)))
  ||| A word, unsigned, in decimal.
  showUnsigned : f (MkPort [Port.Word] (Just (Port.ValueOf String)))

||| Each string routine's entries of two records made one.
public export
zipStringRoutines : ({p : Port} -> f p -> g p -> h p) -> StringRoutines f -> StringRoutines g -> StringRoutines h
zipStringRoutines z a b =
  MkStringRoutines (z a.length b.length) (z a.head b.head) (z a.tail b.tail) (z a.index b.index)
    (z a.cons b.cons) (z a.append b.append) (z a.reverse b.reverse) (z a.substr b.substr) (z a.compare b.compare)
    (z a.showSigned b.showSigned) (z a.showUnsigned b.showUnsigned)

||| The string routines' entries, each with its port.
public export
stringRoutineList : StringRoutines f -> List (p : Port ** f p)
stringRoutineList r =
  [(_ ** r.length), (_ ** r.head), (_ ** r.tail), (_ ** r.index), (_ ** r.cons), (_ ** r.append),
   (_ ** r.reverse), (_ ** r.substr), (_ ** r.compare), (_ ** r.showSigned), (_ ** r.showUnsigned)]
