-- Flat functions of a library, whose flat forms its TTC keeps.
module Digits

-- `putChar` unfolds, with its dictionary, into the Prelude's private
-- primitive, which the Prelude wrote.
%cg native flat Digits.digits
export
digits : Bits64 -> IO ()
digits n = if n < 10 then putChar (digit n)
                     else do digits (n `div` 10)
                             putChar (digit (n `mod` 10))
  where
    digit : Bits64 -> Char
    digit d = cast (cast {to = Bits32} d + 48)
