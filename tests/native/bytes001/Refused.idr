-- A pure load, and a maker of an immutable object from words, are
-- declared only for a type the representation contract states immutable:
-- a buffer of `Data.Buffer` is a `BYTES` object as a `Bytes` is, but
-- written after it is made, so no reader of it may be pure, and no maker
-- of one may be laid out as static data, which no one writes. This file
-- typechecks exactly when both blocks are refused, for that reason.
module Refused

import Data.Buffer
import Native.Types.Bytes
import Native.Types.Repr

failing "Can't find an implementation for Immutable Buffer"
  bufferWord : PureLoad Buffer (signature PayloadWord)

failing "Can't find an implementation for Immutable Buffer"
  bufferMaker : FromWords Buffer
