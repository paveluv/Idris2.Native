-- A pure load is declared only for a type the representation contract
-- states immutable: a buffer of `Data.Buffer` is a `BYTES` object as a
-- `Bytes` is, but written after it is made, so no reader of it may be
-- pure. This file typechecks exactly when the block is refused, for that
-- reason.
module Refused

import Data.Buffer
import Native.Types.Bytes
import Native.Types.Repr

failing "Can't find an implementation for Immutable Buffer"
  bufferWord : PureLoad Buffer (signature PayloadWord)
