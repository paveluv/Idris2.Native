-- Mutable records, natively: a `Struct 2 [String, List Integer]` is one
-- object of the heap, of the kind `STRUCT`, two raw words then two values,
-- each read and written in place. The collector walks it by its header,
-- scanning the two values alone, so the list it holds survives the
-- collections below, and a word that looks like a pointer is left as it is.
--
-- A record is made value by value, in order, each of the type the record
-- has at its index, from its counts, which its type ties them to:
--
--     b <- new 2 2
--     b <- put 0 b (MkUniform "hello")
--     b <- put 1 b (MkUniform [1, 2, 3])
--     s <- done b
--
-- and `done` gives it only once both are stored. An index the type does
-- not allow does not typecheck: the `failing` blocks show three.
module Main

import Native.Flat.Uniform
import Native.Runtime.Space
import Native.Support.StructObj
import Native.Types.Struct

Rec : Type
Rec = Struct 2 [String, List Integer]

-- many short-lived lists, so that the heap is collected many times
churn : Nat -> Nat -> Nat
churn Z acc = acc
churn (S k) acc = churn k (acc + length [1 .. the Integer 200])

failing "Can't find an implementation for Below"
  -- a raw word past the record's two
  third : Uniform Rec -> IO Bits64
  third r = readWord 2 r

failing "Can't find an implementation for FromString (List Integer)"
  -- a string where the record holds a list
  wrong : Uniform Rec -> IO ()
  wrong r = writeValue 1 r (MkUniform "no")

failing "Can't find an implementation for 1 = length [String, List Integer]"
  -- a record given before its second value is stored
  early : IO (Uniform Rec)
  early = do
    b <- new 2 2
    b <- put 0 b (MkUniform "hello")
    done b

-- a new record, its type stated where it is made
made : IO (Uniform Rec)
made = do
  b <- new 2 2
  b <- put 0 b (MkUniform "hello")
  b <- put 1 b (MkUniform [1, 2, 3])
  done b

main : IO ()
main = do
  s <- made
  writeWord 0 s 42
  writeWord 1 s 0x1000          -- looks like an address; the collector never reads it
  printLn (churn 2000 0)
  writeValue 1 s (MkUniform [4, 5])
  printLn (churn 2000 0)
  w0 <- readWord 0 s
  w1 <- readWord 1 s
  t <- readValue 0 s
  l <- readValue 1 s
  printLn (w0, w1, t.value, l.value)
  c <- collectionCount
  putStrLn ("collected: " ++ show (c > 100))
