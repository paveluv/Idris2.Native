-- The runtime reads objects as words, with rules restated from
-- Compiler.Native.HeapObject, which the compiler uses on typed headers:
-- here the two are compared, for every kind with each part at its
-- boundaries, so that a change to one that misses the other is caught.
-- `objectWords` is the size including the header; `scannedWords` the
-- first word that holds a value and how many do.
module Main

import Compiler.Native.HeapObject
import Runtime.Object

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
  [ (_ ** ConH 0 0), (_ ** ConH 1 1), (_ ** ConH 3 7), (_ ** ConH (largest 28) (largest 28))
  , (_ ** ClosureH 1 0), (_ ** ClosureH 4 2), (_ ** ClosureH (largest 28) (largest 28))
  , (_ ** Int64H), (_ ** DoubleH), (_ ** IORefH), (_ ** PtrH)
  , (_ ** StringH True 0), (_ ** StringH False 1), (_ ** StringH True 9), (_ ** StringH False (largest 55))
  , (_ ** BufferH 0), (_ ** BufferH 17), (_ ** BufferH (largest 56))
  , (_ ** BignumH False 0), (_ ** BignumH True 3), (_ ** BignumH True (largest 55))
  , (_ ** ArrayH 0), (_ ** ArrayH 5), (_ ** ArrayH (largest 56)) ]

check : (k : Kind ** Header TestEnc k) -> List String
check (k ** h) =
  let w = cast {to = Bits64} (encodeHeader h)
      id = kindOfHeader w
      size = objectWords id w
      (from, count) = scannedWords id w
      (from', count') = scanned h
  in (if id /= kindId k then [show h ++ ": the kind read is " ++ show id] else [])
     ++ (if size /= cast (HeapObject.objectWords h) then [show h ++ ": " ++ show size ++ " words, not " ++ show (HeapObject.objectWords h)] else [])
     ++ (if (from, count) /= (cast from', cast count') then [show h ++ ": scanned " ++ show (from, count) ++ ", not " ++ show (from', count')] else [])

main : IO ()
main = do
  let failures = concatMap check headers
  traverse_ putStrLn failures
  putStrLn (show (length headers) ++ " headers, " ++ show (length failures) ++ " differences")
  -- a continuation of 3 values and 2 raw words: 7 words, scanned from its parent
  let l = cast {to = Bits64} (layoutWord 3 2)
  putStrLn ("a continuation of 3 values and 2 raw words: " ++ show (continuationWords l) ++ " words, scanned " ++ show (continuationScanned l))
  putStrLn ("forwarded to 0x1000: " ++ (if kindOfHeader (forwardingHeader 0x1000) == forwardingId && forwardedTo (forwardingHeader 0x1000) == 0x1000 then "kind 15, address kept" else "WRONG"))
