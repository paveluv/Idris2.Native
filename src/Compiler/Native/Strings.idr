||| String literals as static objects: the one place in the compiler that
||| lays out a string, as the runtime's string module is the one place in the
||| runtime. A literal is encoded under the program's string encoding when it
||| is compiled, its header set then: under UTF-8 its bytes and the bit that
||| says they are all ASCII; under UTF-32 its code points, four bytes each.
||| Idris's strings hold Unicode scalar values only, so a literal is
||| well-formed under either.
module Compiler.Native.Strings

import Compiler.Native.HeapObject.BignumEnc as HeapObject
import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Header as HeapObject
import Compiler.Native.HeapObject.Kind
import Compiler.Native.HeapObject.StringEnc
import Compiler.Native.HeapObject.ValEnc as HeapObject

import Data.List
import Data.Vect

%default total

||| The static object of a literal under the program's encodings: its header
||| and the words after it.
export
literal : (enc : HeapObject.Enc) -> String ->
          Maybe (h : HeapObject.Header enc HeapObject.Kind.STRING ** Vect (HeapObject.Header.fieldWords h) Int64)
literal enc s = case enc of
  HeapObject.Enc.MkEnc _ _ HeapObject.StringEnc.Utf8 =>
                   let bs = encodeAll utf8 (unpack s)
                       h = HeapObject.Header.StringH (all (< 0x80) bs) (length bs)
                   in map (\ws => (h ** ws)) (toVect _ (words bs))
  HeapObject.Enc.MkEnc _ _ HeapObject.StringEnc.Utf32 =>
                   let cs = unpack s
                       h = HeapObject.Header.StringCharsH (length cs)
                   in map (\ws => (h ** ws)) (toVect _ (words (encodeAll utf32 cs)))
  where
    ||| The UTF-8 bytes of a character, shortest form.
    utf8 : Char -> List Bits8
    utf8 c =
      let n = the Integer (cast (ord c)) in
      if n < 0x80 then [b n]
      else if n < 0x800 then [b (0xC0 + n `div` 64), b (0x80 + n `mod` 64)]
      else if n < 0x10000 then [b (0xE0 + n `div` 4096), b (0x80 + (n `div` 64) `mod` 64), b (0x80 + n `mod` 64)]
      else [ b (0xF0 + n `div` 262144), b (0x80 + (n `div` 4096) `mod` 64)
           , b (0x80 + (n `div` 64) `mod` 64), b (0x80 + n `mod` 64) ]
      where
        b : Integer -> Bits8
        b = cast

    ||| A character's code point as four bytes, least significant first.
    utf32 : Char -> List Bits8
    utf32 c = let n = the Integer (cast (ord c)) in
              [cast n, cast (n `div` 0x100), cast (n `div` 0x10000), cast (n `div` 0x1000000)]

    ||| The bytes of each character, end to end. Appended from the right:
    ||| `concatMap` on lists appends from the left, copying the bytes so far
    ||| again for every character.
    encodeAll : (Char -> List Bits8) -> List Char -> List Bits8
    encodeAll f = foldr (\c, rest => f c ++ rest) []

    ||| Bytes as words, eight to a word, least significant first, the last
    ||| padded with zeros.
    words : List Bits8 -> List Int64
    words [] = []
    -- lint: allow trust-escape: `rest` is eight bytes shorter than `bs`
    words bs = let (w, rest) = splitAt 8 bs in
               word (w ++ replicate (minus 8 (length w)) 0) :: assert_total (words rest)
      where
        word : List Bits8 -> Int64
        word ws = let u = foldr (\x, acc => acc * 256 + the Integer (cast x)) 0 ws in
                  cast (if u >= 9223372036854775808 then u - 18446744073709551616 else u)
