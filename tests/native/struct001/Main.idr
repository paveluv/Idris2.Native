-- Mutable records, natively: a record of named fields is one object of the
-- heap, of the kind `STRUCT`, its raw words then its values, each read and
-- written in place. The collector walks it by its header, scanning the
-- values alone, so the list it holds survives the collections below, and a
-- word that looks like a pointer is left as it is.
--
-- A field is a name and what it holds: `~:` a raw word, of a machine type
-- (or a carrier the collector need not see), `~&` a value of an Idris type.
-- The raw words come first, whatever the order the fields are written in:
-- here `count`, `mark` and `delta` are raw words 0, 1 and 2, `greeting` and
-- `items` values 0 and 1. A field is read and written by its name, as its
-- type: `get "delta" s` is an `Int`, `get "items" s` a `Uniform (List
-- Integer)`, and the index is found where the program is compiled:
--
--     b <- new 3 2                        -- three raw words, two values
--     b <- put "greeting" b (MkUniform "hello")
--     b <- put "items" b (MkUniform [1, 2, 3])
--     s <- done b
--     set "delta" s (-3)
--
-- and `done` gives it only once both values are stored, in their order. A
-- name the record lacks, a value of another type, the values out of
-- order, a record given early, names twice and a value written as a raw
-- word do not typecheck: the `failing` blocks show each.
module Main

import Native.Carrier
import Native.Field
import Native.Flat.Uniform
import Native.Mach
import Native.Runtime.Cell
import Native.Runtime.PortTy
import Native.Runtime.Space
import Native.Support.StructObj
import Native.Types.Struct

Rec : Type
Rec =
  Struct
    [ "count" ~: Mach.U64, "greeting" ~& String, "mark" ~: Mach.U64, "items" ~& List Integer
    , "delta" ~: Mach.IWord ]

-- many short-lived lists, so that the heap is collected many times
churn : Nat -> Nat -> Nat
churn Z acc = acc
churn (S k) acc = churn k (acc + length [1 .. the Integer 200])

failing "Can't find an implementation for Named"
  -- a field the record does not have
  missing : Uniform Rec -> IO Bits64
  missing r = get "size" r

failing "Can't find an implementation for FromString (List Integer)"
  -- a string where the record holds a list
  wrong : Uniform Rec -> IO ()
  wrong r = set "items" r (MkUniform "no")

failing "Can't find an implementation for intToBool 0 = True"
  -- the second value stored first: it is not the value due next
  disorder : IO (Uniform Rec)
  disorder = do
    b <- new 3 2
    b <- put "items" b (MkUniform [1])
    done b

failing "Can't find an implementation for 0 + 1 ="
  -- a record given before its second value is stored
  early : IO (Uniform Rec)
  early = do
    b <- new 3 2
    b <- put "greeting" b (MkUniform "hello")
    done b

failing "Can't find an implementation for distinct"
  -- a name twice
  twice : IO (Uniform (Struct ["count" ~: Mach.U64, "count" ~: Mach.IWord]))
  twice = do
    b <- new 2 0
    done b

failing "Can't find an implementation for scanned"
  -- a value where the collector would not see it
  hidden : List (String, Carrier)
  hidden = ["greeting" ~: Carrier.ValueOf String]

-- a new record, its type stated where it is made
made : IO (Uniform Rec)
made = do
  b <- new 3 2
  b <- put "greeting" b (MkUniform "hello")
  b <- put "items" b (MkUniform [1, 2, 3])
  done b

main : IO ()
main = do
  s <- made
  set "count" s 42
  set "mark" s 0x1000          -- looks like an address; the collector never reads it
  set "delta" s (-3)
  printLn (churn 2000 0)
  set "items" s (MkUniform [4, 5])
  printLn (churn 2000 0)
  n <- get "count" s
  m <- get "mark" s
  d <- get "delta" s
  t <- get "greeting" s
  l <- get "items" s
  printLn (n, m, d, t.value, l.value)
  c <- collectionCount
  putStrLn ("collected: " ++ show (c > 100))
