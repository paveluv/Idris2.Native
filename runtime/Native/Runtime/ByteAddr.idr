||| The address of memory that holds no object (`ByteAddr`): a run of bytes, a
||| range of address space, an area, the allocation window. The heap's
||| objects have addresses of their own (`Memory.Addr`); a byte address is
||| everything else the runtime points at.
|||
||| A byte address is a word, but only an address's arithmetic applies to
||| it: an address plus or less a count of bytes is an address (`offset`,
||| `before`), and two addresses differ by a count (`distance`); an address
||| is never added to another, or multiplied. So an address taken for a
||| count, or a count for an address, does not typecheck. Its constructor
||| is this module's: an address comes from an operation that gives one,
||| and a word becomes one (`fromWord`) only where the runtime keeps or is
||| given addresses as words, the modules the linter's `byte-addr-maker` names.
module Native.Runtime.ByteAddr

import Native.Runtime.Bits

%default total

||| An address of memory that holds no object.
export
record ByteAddr where
  constructor MkByteAddr
  word : Bits64

||| Addresses compare as their words: the later is the greater.
export
Eq ByteAddr where
  a == b = a.word == b.word

export
Ord ByteAddr where
  compare a b = compare a.word b.word
  a < b = a.word < b.word
  a <= b = a.word <= b.word
  a > b = a.word > b.word
  a >= b = a.word >= b.word

||| The address a word is: for the modules that keep addresses as words,
||| or are given them so (`byte-addr-maker`).
export %inline
fromWord : Bits64 -> ByteAddr
fromWord = MkByteAddr

||| The word an address is: to store it, or to hand it to the system.
export %inline
toWord : ByteAddr -> Bits64
toWord r = r.word

||| The address `bytes` past an address, and `bytes` before it.
export %inline
offset : ByteAddr -> (bytes : Bits64) -> ByteAddr
offset r n = MkByteAddr (r.word + n)

export %inline
before : ByteAddr -> (bytes : Bits64) -> ByteAddr
before r n = MkByteAddr (r.word - n)

||| Whether the address is the null one, which no memory has: what the
||| system gives for none.
||| The null address, of no memory.
export %inline
null : ByteAddr
null = MkByteAddr 0

export %inline
isNull : ByteAddr -> Bool
isNull r = r.word == 0

||| The bytes from one address to a later one.
export %inline
distance : (to, from : ByteAddr) -> Bits64
distance a b = a.word - b.word

||| The address rounded up to a multiple of `align`, a power of two.
export %inline
alignUp : ByteAddr -> (align : Bits64) -> ByteAddr
alignUp r a = MkByteAddr ((r.word + (a - 1)) .&. (0 - a))
