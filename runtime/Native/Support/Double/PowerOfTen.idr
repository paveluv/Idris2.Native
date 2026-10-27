||| The powers of ten as a table (`powerOfTen`), which the conversions
||| between doubles and their decimal text multiply by. The native code
||| generator makes it as it compiles a program that may show or read a
||| double, since those conversions are string routines, which it compiles
||| with a program whose code may call them; or one that reads it itself.
||| It lays it out in the read-only data of a program whose code reaches
||| it, each row two loads where it is read; another code generator makes
||| it as any other constant.
module Native.Support.Double.PowerOfTen

import Native.Support.Table
import Native.Support.Table.Row

%default total

||| The 128-bit significand of 10^k, rounded down: the high word and the low
||| word of the number m, 2^127 <= m < 2^128, such that 10^k = m * 2^e
||| exactly for some e, or the largest such m below it where there is none.
||| 10^k is 5^k * 2^k, so its significand is 5^k's: exact for k from 0 to
||| 55, where 5^k fits in 128 bits; for a negative k, a power of two
||| divided by 5^-k, the one that puts the quotient's top bit at 127.
||| Computed as `Integer`s, for a k from -4003 to 4003, as `fiveBits` asks,
||| which the table's (`powerOfTen`) all are.
export covering
significand : Int -> (Bits64, Bits64)
significand k =
  let e : Integer = cast k
      m = if e >= 0 then shifted (power 5 e) (fiveBits e)
          else divided (power 5 (negate e)) (fiveBits (negate e))
  in (cast (prim__shr_Integer m 64), cast m)
  where
    ||| The number of bits of 5^a, for a from 0 to 4003, with no search:
    ||| the floor of a * log2 5, plus one, log2 5 taken as 1217359 / 2^19,
    ||| which is below it by less than 10^-7, too little to move the floor
    ||| at any of these a, though it does at 4004.
    fiveBits : Integer -> Integer
    fiveBits a = prim__shr_Integer (a * 1217359) 19 + 1

    ||| b to the power e, for e >= 0, by squaring.
    power : (b, e : Integer) -> Integer
    power b 0 = 1
    power b e =
      let h = power b (e `div` 2)
          h2 = h * h
      in if e `mod` 2 == 0 then h2 else h2 * b

    ||| A positive integer of `bits` bits shifted so that its top bit is bit
    ||| 127: up, or down, the bits shifted out dropped.
    shifted : (v, bits : Integer) -> Integer
    shifted v bits =
      if bits <= 128 then prim__shl_Integer v (128 - bits) else prim__shr_Integer v (bits - 128)

    ||| 2^(bits + 127) divided by a positive integer of `bits` bits that is
    ||| no power of two, as 5^n is for an n of 1 or more, rounded down: a
    ||| quotient whose top bit is bit 127; of a power of two, the quotient
    ||| is 2^128.
    divided : (d, bits : Integer) -> Integer
    divided d bits = prim__shl_Integer 1 (bits + 127) `div` d

%cg native static Support.Double.PowerOfTen.powerOfTen
||| Row k the significand of 10^k (`significand`), for k from -342 to 326,
||| what both conversions reach: printing from 10^-292 to 10^326, reading
||| from 10^-342 to 10^308. Marked static, so that the native code
||| generator computes its rows as it compiles a program, into one object
||| of the program's read-only data, which flat code reads at its address;
||| another code generator makes it as any other constant (`Table` says
||| how).
export covering
powerOfTen : Table (-342) 326 (Bits64, Bits64)
powerOfTen = Table.tabulate significand
