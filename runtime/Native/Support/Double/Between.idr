||| Which of two adjacent doubles a long decimal is nearer (`between`), when
||| its first 19 digits leave it unsure: exactly, by comparing it with the
||| point halfway between them, the decimal in limbs (`Limbs`).
module Native.Support.Double.Between

import Native.Support.Double.Limbs

import Native.Runtime.Bits
import Native.Runtime.Ordo as Runtime
import Native.Support.Obj

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The bits of the double nearest the decimal `digits * 10^e10`, of the two
||| that are the double of bits `below`, positive, and the next one up,
||| bits `below + 1`: the lower if the decimal is below the halfway point
||| between them, the upper if above, the one of the even significand if
||| on it. `sticky` says the decimal has nonzero digits beyond `digits`, so
||| that it is above the halfway point where `digits` is on it. The digits
||| are a number in limbs, which the comparison changes.
export covering
between : (digits : Limbs) -> (sticky : Bool) -> (e10 : Int) -> (below : Bits64) ->
          Runtime.Ordo.Op Runtime.Ordo Bits64
between d sticky e10 b = do
  -- the halfway point, (2m + 1) * 2^(e2 - 1), of the lower double m * 2^e2
  let biased = b `shiftR` 52
      fraction = b .&. 0xFFFFFFFFFFFFF
      m = if biased == 0 then fraction else fraction .|. 0x10000000000000
      e2 : Int = if biased == 0 then -1074 else cast biased - 1075
      f2 = e2 - 1
  y <- Limbs.newLimbs
  Limbs.setWord y (2 * m + 1)
  -- digits * 5^e10 * 2^e10 against y * 2^f2, each side made an integer, then
  -- the one of the larger power of two shifted to the other's
  if e10 >= 0
     then do
       Limbs.mulPow5 d (cast e10)
       if e10 >= f2 then Limbs.shiftLeft d (cast (e10 - f2))
         else Limbs.shiftLeft y (cast (f2 - e10))
     else do
       Limbs.mulPow5 y (cast (negate e10))
       if f2 >= e10 then Limbs.shiftLeft y (cast (f2 - e10))
         else Limbs.shiftLeft d (cast (e10 - f2))
  c <- Limbs.compareLimbs d y
  Runtime.Ordo.pure $
    if c < 0 then b
    else if c > 0 || sticky then b + 1
    else if b .&. 1 == 0 then b else b + 1
