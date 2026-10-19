-- Numbers as text, both ways, against Chez: the casts from strings to
-- doubles and to every integer type, and `show` of what they give, over the
-- texts where the native backend reads and writes as Chez does. Where the
-- native backend follows what every code generator does rather than Chez
-- alone (the comments of `readDouble`, `readWord` and `showDouble` say
-- where), the two part: an exact tie printed with the even digit, a
-- subnormal without `|n`, -0 read as -0.0, an exponent in an integer's
-- text; none of those is here.
--
-- A double comes from a text, not a literal, so that the program needs no
-- double arithmetic of its own; `show` of it is Dragonbox's shortest digits,
-- in Chez's layout.
module Main

doubles : List String
doubles =
  [ "0.0", "-0.0", "1.0", "0.1", "0.3", "2.5", "-3.75", "1e21", "1e22", "1e23", "123456789012.0"
  , "1e-7", "0.001", "1e-4", "9007199254740993", "1.7976931348623157e308", "2.2250738585072014e-308"
  , "4.9e-300", "+inf.0", "-inf.0", "+nan.0", "1e400", "-1e400", "1e-400", "3.141592653589793"
  , "2.718281828459045", "12345.6789", "1E5", "+5", ".5", "5.", "123456789012345678901234567890",
    "0.1e1"
  , "", "abc", " 1", "1e", "--1", "1.2.3" ]

integers : List String
integers =
  [ "0", "12", "-5", "+5", "007", "12.7", "-12.7", ".5", "127", "128", "-129", "255", "256", "300",
    "-1"
  , "32768", "65536", "2147483648", "-2147483649", "4294967296", "9223372036854775807"
  , "9223372036854775808", "-9223372036854775809", "18446744073709551616"
  , "", " 12", "12abc", "0x10", "1/2", "+-5" ]

double : String -> String
double t = show t ++ " " ++ show (the Double (cast t))

integer : String -> String
integer t = show t ++ " " ++ show (the Int (cast t)) ++ " " ++ show (the Int8 (cast t)) ++ " "
  ++ show (the Int16 (cast t))
  ++ " " ++ show (the Int32 (cast t)) ++ " " ++ show (the Int64 (cast t)) ++ " "
    ++ show (the Bits8 (cast t))
  ++ " " ++ show (the Bits16 (cast t)) ++ " " ++ show (the Bits32 (cast t)) ++ " "
    ++ show (the Bits64 (cast t))

main : IO ()
main = do
  traverse_ (putStrLn . double) doubles
  traverse_ (putStrLn . integer) integers
