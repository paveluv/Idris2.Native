-- One error of a signature, with the field that makes a record not flat.
record Labelled where
  constructor MkLabelled
  label : String
  value : Bits64

-- A record is flat when its run-time fields are: `value` is, `label` is
-- not, though the function never reads it, since the whole record is the
-- argument. Erased, `0 label : String` would take no part. The reason names
-- the field that is not flat.
%cg native flat Main.weight
weight : Labelled -> Bits64
weight w = w.value

main : IO ()
main = pure ()
