-- The collector knows objects by their shape only (HeapObj.Shape): from a
-- header word, an object's size and which of its words hold values. Each
-- kind of object is laid out as a shape. Here each kind's layout, as its
-- documentation in HeapObj.Kind describes it, is written out by hand
-- (`layout`), and compared with the shape description twice: as the
-- compiler reads it, from a typed header (`objectWords`, `scanned`), and
-- as the collector reads it, from the header's word (`objectWordsOf`,
-- `scannedOf`). Every kind is checked with each part at its boundaries,
-- so that a change to a shape, or to the shape a kind has, that breaks a
-- kind's layout is caught. The word must also carry the kind's shape and
-- tag in its low bits.
module Main

import Native.HeapObj.BignumEnc
import Native.HeapObj.Enc
import Native.HeapObj.Header
import Native.HeapObj.Kind
import Native.HeapObj.LayoutWord
import Native.HeapObj.Shape
import Native.HeapObj.StringEnc
import Native.HeapObj.ValEnc

TestEnc : Enc
TestEnc = MkEnc FixnumTag1 (MkBignumEnc Limb64 SignMagnitude) Utf8

largest : Nat -> Nat
largest w = cast (pow2 w - 1)
  where
    pow2 : Nat -> Integer
    pow2 Z = 1
    pow2 (S n) = 2 * pow2 n

headers : List (k : Kind ** Header TestEnc k)
headers =
  [ (_ ** ConH 0 0), (_ ** ConH 1 1), (_ ** ConH 3 7), (_ ** ConH (largest 20) (largest 28))
  , (_ ** ClosureH 1 0), (_ ** ClosureH 4 2), (_ ** ClosureH (largest 16) (largest 28))
  , (_ ** Int64H), (_ ** DoubleH), (_ ** IORefH), (_ ** PtrH)
  , (_ ** StringH True 0), (_ ** StringH False 1), (_ ** StringH True 9), (_ ** StringH False (largest 47))
  , (_ ** BufferH 0), (_ ** BufferH 17), (_ ** BufferH (largest 47))
  , (_ ** BignumH False 0), (_ ** BignumH True 3), (_ ** BignumH True (largest 44))
  , (_ ** ArrayH 0), (_ ** ArrayH 5), (_ ** ArrayH (largest 28)) ]

-- The words that so many bytes fill, padded to whole words.
padded : Nat -> Nat
padded n = cast ((the Integer (cast n) + 7) `div` 8)

-- Each kind's layout, by hand: its words, the header included, and the
-- first word that holds a value and how many do.
layout : Header TestEnc k -> (Nat, (Nat, Nat))
layout (ConH _ a) = (1 + a, (1, a))             -- the fields, all values
layout (ClosureH _ f) = (2 + f, (2, f))         -- the code's address, then the arguments
layout Int64H = (2, (1, 0))                     -- the bits, raw
layout DoubleH = (2, (1, 0))
layout PtrH = (2, (1, 0))
layout (StringH _ n) = (1 + padded n, (1, 0))   -- the bytes, raw
layout (StringCharsH n) = (1 + padded (4 * n), (1, 0))
layout (BignumH _ n) = (1 + n, (1, 0))          -- the limbs, raw
layout IORefH = (2, (1, 1))                     -- the one value
layout (ArrayH n) = (1 + n, (1, n))             -- the elements, all values
layout (BufferH n) = (1 + padded n, (1, 0))

check : (k : Kind ** Header TestEnc k) -> List String
check (k ** h) =
  let w = cast {to = Bits64} (encodeHeader h)
      typed = (objectWords h, scanned h)
      (size, (from, count)) = (objectWordsOf w, scannedOf w)
      words = (cast {to = Nat} size, (cast {to = Nat} from, cast {to = Nat} count))
  in (if Just (shapeIdOf w) /= map shapeId (shapeOf k) then [show h ++ ": the shape read is " ++ show (shapeIdOf w)] else [])
     ++ (if field {s = VALUES} Tag w /= tagOf k then [show h ++ ": the tag read is " ++ show (field {s = VALUES} Tag w)] else [])
     ++ (if typed /= layout h then [show h ++ ": the compiler reads " ++ show typed ++ ", not " ++ show (layout h)] else [])
     ++ (if words /= layout h then [show h ++ ": the collector reads " ++ show words ++ ", not " ++ show (layout h)] else [])

main : IO ()
main = do
  let failures = concatMap check headers
  traverse_ putStrLn failures
  putStrLn (show (length headers) ++ " headers, " ++ show (length failures) ++ " differences")
  -- a continuation of 3 values and 2 raw words: 7 words, scanned from its parent
  let l = cast {to = Bits64} (layoutWord 3 2)
  putStrLn ("a continuation of 3 values and 2 raw words: " ++ show (continuationWords l) ++ " words, scanned " ++ show (continuationScanned l))
  putStrLn ("forwarded to 0x1000: " ++ (if isForwarding (forwardingHeader 0x1000) && forwardedTo (forwardingHeader 0x1000) == 0x1000 then "id 15, address kept" else "WRONG"))
