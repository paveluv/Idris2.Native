-- `cast` from a String to each integer type of 64 bits or fewer,
-- natively: the text every code generator's cast reads, a sign and digits
-- with at most one point among them; its value the decimal's truncated
-- toward zero, then wrapped to the type's width as a cast from Integer is
-- (300 is 44 as a Bits8, -1 is 255); 0 for any other text, an exponent, a
-- space, a hexadecimal prefix, a ratio and other digits than ASCII's among
-- them. Each line is a text, then its value as Int, Int8, Int16, Int32,
-- Int64, Bits8, Bits16, Bits32 and Bits64. The values are Python's, by the
-- same rule.
module Main

texts : List String
texts =
  [ ""
  , "0"
  , "12"
  , "-5"
  , "+5"
  , "007"
  , "5."
  , "12.7"
  , "-12.7"
  , ".5"
  , "-.5"
  , "-0"
  , "+0.0"
  , "127"
  , "128"
  , "-128"
  , "-129"
  , "255"
  , "256"
  , "300"
  , "-1"
  , "32767"
  , "32768"
  , "65535"
  , "65536"
  , "2147483647"
  , "2147483648"
  , "-2147483648"
  , "-2147483649"
  , "4294967295"
  , "4294967296"
  , "9223372036854775807"
  , "9223372036854775808"
  , "-9223372036854775808"
  , "-9223372036854775809"
  , "18446744073709551615"
  , "18446744073709551616"
  , "123456789012345678901234567890"
  , "123456789012345678901234.5"
  , "-123456789012345678901234567890"
  , "1e3"
  , " 12"
  , "12 "
  , "12abc"
  , "0x10"
  , "1/2"
  , "+-5"
  , "--5"
  , "."
  , "+"
  , "-"
  , "1.2.3"
  , "١٢" ]

line : String -> String
line t = show t ++ " " ++ show (the Int (cast t)) ++ " " ++ show (the Int8 (cast t)) ++ " "
  ++ show (the Int16 (cast t))
  ++ " " ++ show (the Int32 (cast t)) ++ " " ++ show (the Int64 (cast t)) ++ " "
    ++ show (the Bits8 (cast t))
  ++ " " ++ show (the Bits16 (cast t)) ++ " " ++ show (the Bits32 (cast t)) ++ " "
    ++ show (the Bits64 (cast t))

main : IO ()
main = traverse_ (putStrLn . line) texts
