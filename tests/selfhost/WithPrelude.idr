||| The ladder's second module to check: one with the Prelude, so checking
||| it reads the Prelude's TTCs and elaborates against them: interfaces,
||| their implementations found by search, numeric literals.
module WithPrelude

%default total

sumTo : Nat -> Nat
sumTo Z = 0
sumTo (S k) = S k + sumTo k

main : IO ()
main = printLn (sumTo 10, map (* 2) [1, 2, 3])
