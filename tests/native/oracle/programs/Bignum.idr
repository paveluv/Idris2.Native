-- Integer arithmetic beyond 64 bits: products, powers, division and
-- remainder with negative operands. An `Integer` that fits a fixnum is one;
-- any other is a bignum object, its sign and 64-bit limbs.
module Main

fact : Integer -> Integer
fact 0 = 1
fact n = n * fact (n - 1)

power : Integer -> Integer -> Integer
power b 0 = 1
power b e = b * power b (e - 1)

fib : Integer -> Integer -> Integer -> Integer
fib 0 a _ = a
fib n a b = fib (n - 1) b (a + b)

main : IO ()
main = do
  printLn (fact 30)
  printLn (power 2 100)
  printLn (fact 40 `div` fact 38)
  printLn (fact 40 `mod` 1000000007)
  printLn (negate (fact 25) `div` 7, negate (fact 25) `mod` 7)
  printLn (fib 300 0 1)
  printLn (power 3 50 - power 3 50 + 1)
