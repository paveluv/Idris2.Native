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
-- type: `get "delta" s` is an `Int`, `get "items" s` a `List Integer`,
-- and the index is found where the program is compiled:
--
--     b <- new                            -- its counts found from its fields
--     b <- put "greeting" b "hello"
--     b <- put "items" b [1, 2, 3]
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
  missing : Rec -> IO Bits64
  missing r = get "size" r

failing "Can't find an implementation for FromString (List Integer)"
  -- a string where the record holds a list
  wrong : Rec -> IO ()
  wrong r = set "items" r "no"

failing "Can't find an implementation for intToBool 0 = True"
  -- the second value stored first: it is not the value due next
  disorder : IO Rec
  disorder = do
    b <- new
    b <- put "items" b [1]
    done b

failing "Can't find an implementation for intToBool (2 == (0 + 1))"
  -- a record given before its second value is stored
  early : IO Rec
  early = do
    b <- new
    b <- put "greeting" b "hello"
    done b

failing "Can't find an implementation for distinct"
  -- a name twice
  twice : IO (Struct ["count" ~: Mach.U64, "count" ~: Mach.IWord])
  twice = do
    b <- new
    done b

failing "Can't find an implementation for scanned"
  -- a value where the collector would not see it
  hidden : List (String, Carrier)
  hidden = ["greeting" ~: Carrier.ValueOf String]

-- a new record, its type stated where it is made
made : IO Rec
made = do
  b <- new
  b <- put "greeting" b "hello"
  b <- put "items" b [1, 2, 3]
  done b

main : IO ()
main = do
  s <- made
  set "count" s 42
  set "mark" s 0x1000          -- looks like an address; the collector never reads it
  set "delta" s (-3)
  printLn (churn 2000 0)
  set "items" s [4, 5]
  printLn (churn 2000 0)
  n <- get "count" s
  m <- get "mark" s
  d <- get "delta" s
  t <- get "greeting" s
  l <- get "items" s
  printLn (n, m, d, t, l)
  c <- collectionCount
  putStrLn ("collected: " ++ show (c > 100))
