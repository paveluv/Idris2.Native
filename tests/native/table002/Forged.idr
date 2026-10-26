-- A table is made only by `tabulate`, whose rows are always as many words
-- as its range and its row type say, so that a read of a row may load its
-- words unchecked. A module that imports the tables can neither make one
-- of other words, such as a table of ten rows over one word, which a read
-- of row 9 would load past, nor take the words out of one, nor take one
-- apart: the constructor and the field are the tables' module's alone.
-- This file typechecks exactly when the three blocks are refused, for
-- that reason.
module Forged

import Native.Support.Table
import Native.Types.Bytes

failing "Name Native.Support.Table.MkTable is private"
  forged : Table 0 9 Bits64
  forged = MkTable (generate 1 (\_ => 0))

failing "Name Native.Support.Table.Table.(.rows) is private"
  peek : Table 0 9 Bits64 -> Bytes
  peek t = t.rows

failing "Name Native.Support.Table.MkTable is private"
  apart : Table 0 9 Bits64 -> Bytes
  apart (MkTable b) = b
