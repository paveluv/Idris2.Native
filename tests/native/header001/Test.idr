-- The header encoding of HeapObj.Header. Decoding a header's encoding gives
-- the header back, for every kind with each part at 0, 1 and its largest
-- value; a part one beyond its width does not fit; words that no header
-- encodes are rejected; and under bignums in two's complement, whose header
-- does not exist yet, no BIGNUM header decodes.
--
-- Every object on the heap starts with a header word: its kind, and the
-- parts that say how big it is and what it holds. `Just x` is a CON, a
-- constructor's object, of constructor id 1 and arity 1, its field `x`
-- after the header; a closure's header holds the function's arity and the
-- number of arguments filled; a string's, its number of bytes. Compiled
-- code writes the header when it allocates and reads the constructor id in
-- a `case`; the collector reads the size and which words to scan.
module Main

import Data.List
import HeapObj.BignumEnc
import HeapObj.Enc
import HeapObj.Header
import HeapObj.Kind
import HeapObj.LayoutWord
import HeapObj.StringEnc
import HeapObj.ValEnc

||| The encodings the headers are under: bignums in sign-magnitude, whose
||| header holds the sign.
TestEnc : Enc
TestEnc = MkEnc FixnumTag1 (MkBignumEnc Limb64 SignMagnitude) Utf8

largest : (width : Nat) -> Nat
largest w = cast (pow2 w - 1)
  where
    pow2 : Nat -> Integer
    pow2 Z = 1
    pow2 (S n) = 2 * pow2 n

headers : List (k : Kind ** Header TestEnc k)
headers =
  [ (_ ** ConH 0 0), (_ ** ConH 1 1), (_ ** ConH (largest 28) (largest 28))
  , (_ ** ClosureH 1 0), (_ ** ClosureH (largest 28) (largest 28))
  , (_ ** Int64H), (_ ** DoubleH), (_ ** IORefH), (_ ** PtrH)
  , (_ ** StringH True 0), (_ ** StringH False 1), (_ ** StringH True (largest 55))
  , (_ ** BufferH 0), (_ ** BufferH (largest 56))
  , (_ ** BignumH False 0), (_ ** BignumH True 1), (_ ** BignumH True (largest 55))
  , (_ ** ArrayH 0), (_ ** ArrayH 1), (_ ** ArrayH (largest 56)) ]

roundTrips : (k : Kind ** Header TestEnc k) -> Bool
roundTrips (_ ** h) = case decodeHeader TestEnc (encodeHeader h) of
  Just (_ ** h') => sameHeader h h'
  Nothing => False

tooWide : List (k : Kind ** Header TestEnc k)
tooWide =
  [ (_ ** ConH (largest 28 + 1) 0), (_ ** ConH 0 (largest 28 + 1))
  , (_ ** ClosureH (largest 28 + 1) 0), (_ ** ClosureH 0 (largest 28 + 1))
  , (_ ** StringH False (largest 55 + 1)), (_ ** BufferH (largest 56 + 1))
  , (_ ** BignumH False (largest 55 + 1)), (_ ** ArrayH (largest 56 + 1)) ]

noHeader : List (String, Int64)
noHeader =
  [ ("kind 0", 0), ("the CONT id", 11), ("kind 12", 12)
  , ("kind 15, the forwarding header", 15)
  , ("an INT64 with a flag set", 3 + 16)
  , ("an INT64 with a bit beyond its parts", 3 + 256)
  , ("a CON with the mark bit set", encodeHeader (ConH 1 2) + 16)
  , ("all ones", -1) ]

samples : List (k : Kind ** Header TestEnc k)
samples = [ (_ ** ConH 1 2), (_ ** ClosureH 3 1), (_ ** StringH True 9), (_ ** BignumH True 2), (_ ** IORefH), (_ ** ArrayH 4) ]

hex : Int64 -> String
hex w = pack (map digit (reverse (go 16 (if w < 0 then cast w + 18446744073709551616 else cast w))))
  where
    digit : Integer -> Char
    digit d = if d < 10 then chr (cast d + 48) else chr (cast d + 87)
    go : Nat -> Integer -> List Integer
    go Z _ = []
    go (S n) u = (u `mod` 16) :: go n (u `div` 16)

main : IO ()
main = do
  let failed = filter (not . roundTrips) headers
  putStrLn ("round trip: " ++ show (length headers) ++ " headers, " ++ show (length failed) ++ " failed")
  traverse_ (\(_ ** h) => putStrLn ("  failed: " ++ show h)) failed
  putStrLn ("too wide for fits: " ++ show (length (filter (\(_ ** h) => not (fits h)) tooWide)) ++ " of " ++ show (length tooWide))
  traverse_ (\(what, w) => putStrLn (what ++ ": " ++ maybe "rejected" (const "ACCEPTED") (decodeHeader TestEnc w))) noHeader
  let twos = MkEnc FixnumTag1 (MkBignumEnc Limb64 TwosComplement) Utf8
  putStrLn ("a BIGNUM header under two's complement: "
            ++ maybe "rejected" (const "ACCEPTED") (decodeHeader twos (encodeHeader {enc = TestEnc} (BignumH True 2))))
  putStrLn ("ConH 1 2 encodes as 0x" ++ hex (encodeHeader (ConH 1 2)))
  traverse_ (\(_ ** h) => putStrLn (show h ++ ": " ++ show (objectWords h) ++ " words, scanned " ++ show (scanned h))) samples
