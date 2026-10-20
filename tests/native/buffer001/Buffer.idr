-- Buffers, natively: a buffer is an object of the heap of its bytes,
-- zero when it is made, each read and write of it checked to lie inside
-- it. A number of several bytes is stored little-endian, and a signed
-- one read back with its sign. The Chez backend gives the same, over its
-- bytevectors.
--
-- In surface Idris, base's
--
--     setBits16 buf offset val = primIO (prim__setBits16 buf offset val)
--
-- where the runtime stores the value's two bytes, the low one first, at
-- the offset; `getBits16` reads them back. A file's bytes are read into a
-- buffer from the file's input buffer first, then straight from the
-- system, so the buffer of 200000 bytes below passes through no other.
--
-- Bytes that are not UTF-8 become U+FFFD as they become a string, as
-- Chez's `utf8->string` replaces them: a byte that cannot begin a
-- character, or a sequence cut short, one U+FFFD; a sequence of the
-- length its lead byte says that is an overlong form, a surrogate or
-- past U+10FFFF, one U+FFFD for all its bytes.
module Main

import Data.Buffer
import Data.List
import System.File

main : IO ()
main = do
  Just b <- newBuffer 64
    | Nothing => putStrLn "newBuffer failed"
  putStrLn ("size " ++ show !(rawSize b) ++ ", zero " ++ show !(bufferData b))
  setBits8 b 0 255
  setBits16 b 1 0xABCD
  setBits32 b 3 0xDEADBEEF
  setBits64 b 7 0x0123456789ABCDEF
  setInt8 b 15 (-2)
  setInt16 b 16 (-300)
  setInt32 b 18 (-70000)
  setInt64 b 22 (-5000000000)
  setInt b 30 (-9223372036854775807 - 1)
  setDouble b 38 (cast "-0.1")
  setByte b 46 0x1FF
  putStrLn (show !(getBits8 b 0) ++ " " ++ show !(getBits16 b 1) ++ " " ++ show !(getBits32 b 3)
            ++ " " ++ show !(getBits64 b 7))
  putStrLn (show !(getInt8 b 15) ++ " " ++ show !(getInt16 b 16) ++ " " ++ show !(getInt32 b 18)
            ++ " " ++ show !(getInt64 b 22) ++ " " ++ show !(getInt b 30))
  putStrLn (show !(getDouble b 38) ++ " " ++ show !(getByte b 46) ++ " " ++ show !(getBits8 b 15))
  putStrLn ("bytes " ++ show !(bufferData b))
  -- strings, and copies that overlap
  let s = "héllo, wörld"
  setString b 48 s
  putStrLn (show (stringByteLength s) ++ " bytes: " ++ show !(getString b 48 (stringByteLength s)))
  copyData b 48 8 b 50
  putStrLn ("copied up: " ++ show !(getString b 48 10))
  copyData b 50 8 b 48
  putStrLn ("copied down: " ++ show !(getString b 48 10))
  Just r <- resizeBuffer b 4
    | Nothing => putStrLn "resizeBuffer failed"
  Just c <- concatBuffers [r, r]
    | Nothing => putStrLn "concatBuffers failed"
  putStrLn ("resized and doubled: " ++ show !(bufferData c))
  -- a buffer larger than a file's input buffer, written and read back
  Just big <- newBuffer 200000
    | Nothing => putStrLn "newBuffer failed"
  traverse_ (\i => setBits8 big (i * 997) (cast i)) [0 .. 200]
  Right () <- writeBufferToFile "big.bin" big 200000
    | Left (e, n) => putStrLn ("writeBufferToFile: " ++ show e ++ " after " ++ show n)
  Right back <- createBufferFromFile "big.bin"
    | Left e => putStrLn ("createBufferFromFile: " ++ show e)
  same <- traverse (\i => pure (!(getBits8 big i) == !(getBits8 back i))) [0, 997 .. 199400]
  putStrLn ("read back " ++ show !(rawSize back) ++ " bytes, the same: " ++ show (and (map delay same)))
  -- a line read first, then the rest into a buffer: the bytes the line
  -- left in the file's input buffer come first
  Right () <- writeFile "lines.txt" "one\ntwo\nthree\n"
    | Left e => putStrLn ("writeFile: " ++ show e)
  Right h <- openFile "lines.txt" Read
    | Left e => putStrLn ("openFile: " ++ show e)
  Right l <- fGetLine h
    | Left e => putStrLn ("fGetLine: " ++ show e)
  Just rest <- newBuffer 20
    | Nothing => putStrLn "newBuffer failed"
  Right n <- readBufferData h rest 0 20
    | Left e => putStrLn ("readBufferData: " ++ show e)
  putStrLn ("line " ++ show l ++ ", then " ++ show n ++ " bytes: " ++ show !(getString rest 0 n)
            ++ ", end " ++ show !(fEOF h))
  closeFile h
  Right () <- removeFile "big.bin"
    | Left e => putStrLn ("removeFile: " ++ show e)
  Right () <- removeFile "lines.txt"
    | Left e => putStrLn ("removeFile: " ++ show e)
  -- bytes that are not UTF-8, each run shown as the code points it becomes
  traverse_ (\bs => do
      Just u <- newBuffer (cast (length bs))
        | Nothing => putStrLn "newBuffer failed"
      traverse_ (\(i, v) => setByte u i v) (zip [0 .. cast (length bs) - 1] bs)
      t <- getString u 0 (cast (length bs))
      putStrLn (show bs ++ ": " ++ show (map ord (unpack t))))
    [ [0xC0, 0x80], [0xED, 0xA0, 0x80], [0xF4, 0x90, 0x80, 0x80], [0xE2, 0x82], [0x80, 0x41]
    , [0xE2, 0x41, 0x82], [0xF0, 0x9F, 0x98, 0x80], [0xFF] ]
  putStrLn "done"
