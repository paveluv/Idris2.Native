record Labelled where
  constructor MkLabelled
  label : String
  value : Bits64

-- The reason names the field that is not flat.
%cg native flat Main.weight
weight : Labelled -> Bits64
weight w = w.value

main : IO ()
main = pure ()
