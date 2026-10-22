||| A raw word as what it holds (`Cell`): the state's words and a mutable
||| record's raw fields are words in memory, each of the type its carrier
||| gives it, and a word becomes that type, and the type that word, here.
|||
||| By the type, an interface, so that the conversion is chosen where the
||| program is compiled: an access of a word of one type is that access
||| alone, with no case on what the word holds. A byte address is made from
||| a word here, as the runtime's core keeps byte addresses in its cells.
module Native.Runtime.Cell

import Native.Runtime.ByteAddr

%default total

||| What a raw word can hold, and how it is that word.
public export
interface Cell t where
  fromCell : Bits64 -> t
  toCell : t -> Bits64

public export
Cell ByteAddr where
  fromCell = ByteAddr.fromWord
  toCell = ByteAddr.toWord

public export
Cell Bits64 where
  fromCell w = w
  toCell w = w

||| A signed word, its bits the word's.
public export
Cell Int where
  fromCell = cast
  toCell = cast
