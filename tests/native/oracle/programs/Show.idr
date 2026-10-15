-- Numbers as text at their edges, against Chez: each machine integer type's
-- least and greatest values, with zero and minus one, an `Integer` at the
-- edges of the fixnums, and characters cast to strings, one byte to four
-- in UTF-8.
module Main

main : IO ()
main = do
  printLn [the Int8 (-128), 127, 0, -1]
  printLn [the Int16 (-32768), 32767]
  printLn [the Int32 (-2147483648), 2147483647]
  printLn [the Int64 (-9223372036854775808), 9223372036854775807]
  printLn [the Int (-9223372036854775808), 9223372036854775807, 0, -1]
  printLn [the Bits8 0, 255]
  printLn [the Bits16 0, 65535]
  printLn [the Bits32 0, 4294967295]
  printLn [the Bits64 0, 18446744073709551615]
  printLn [the Integer 0, -1, -4611686018427387904, 4611686018427387903]
  putStrLn (cast 'x' ++ cast 'é' ++ cast '€' ++ cast '𝄞')
