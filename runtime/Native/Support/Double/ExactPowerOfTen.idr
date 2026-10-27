||| The powers of ten that are doubles exactly as a table
||| (`exactPowerOfTen`), which Clinger's fast path for reading a decimal
||| multiplies and divides by. The native code generator makes it as it
||| compiles a program that may read a double, since the reading of a
||| decimal is a string routine, which it compiles with a program whose
||| code may call it; or one that reads it itself. It lays it out in the
||| read-only data of a program whose code reaches it, each row one load
||| where it is read; another code generator makes it as any other
||| constant.
module Native.Support.Double.ExactPowerOfTen

import Native.Support.Table
import Native.Support.Table.Row

%default total

||| 10^k as a double, for k >= 0: 10^k exactly for k from 0 to 22, where
||| 5^k is below 2^53.
export covering
exact : Int -> Double
exact k = cast (power k)
  where
    ||| 10^j as an `Integer`, for j >= 0.
    power : Int -> Integer
    power 0 = 1
    power j = 10 * power (j - 1)

%cg native static Support.Double.ExactPowerOfTen.exactPowerOfTen
||| Row k 10^k as a double (`exact`), for k from 0 to 22, every one of them
||| a double exactly. Marked static, so that the native code generator
||| computes its rows as it compiles a program, into one object of the
||| program's read-only data, which flat code reads at its address; another
||| code generator makes it as any other constant (`Table` says how).
export covering
exactPowerOfTen : Table 0 22 Double
exactPowerOfTen = Table.tabulate exact
