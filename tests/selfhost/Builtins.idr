||| The ladder's first module to check: one that needs nothing but the
||| compiler's own builtins, so checking it reads no TTC of a library.
module Builtins

%default total

data Two = One | Other

swap : Two -> Two
swap One = Other
swap Other = One
