||| Natural numbers of up to 6144 bits in 64-bit limbs (`Limbs`), the few
||| operations that decide a decimal's double exactly need: setting one to a
||| word, multiplying by a word and adding one, multiplying by a power of
||| five, shifting left, and comparing, each over the limbs' kernels
||| (`Native.Support.Bignum.Run`). A number is a byte buffer: its count of
||| limbs in use at word 0, then its limbs from the lowest, with no zero
||| limb on top.
module Native.Support.Double.Limbs

-- lint: allow public-import: `Limbs` is an object of a kind, which an
-- importer's code reduces
import public Native.Types.Kind

import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Bits
import Native.Runtime.Ordo as Runtime
import Native.Support.Bignum.Run as Bignum
import Native.Support.Obj
import Native.Types.Header

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| A natural number in limbs.
public export
Limbs : Type
Limbs = Obj Types.Kind.BUFFER

||| The limbs a number may have: 96, 6144 bits, more than the decision of
||| any decimal's double takes (some 3300).
capacity : Bits64
capacity = 96

||| The count of limbs in use, and setting it.
count : Limbs -> Runtime.Ordo.Op Runtime.Ordo Bits64
count x = Obj.load64 x 0

setCount : Limbs -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo ()
setCount x n = Obj.store64 x 0 n

||| The number's limbs, after its count.
run : Limbs -> Bignum.Run Types.Kind.BUFFER
run x = Bignum.MkRun x 8

||| A new number, zero.
export
newLimbs : Runtime.Ordo.Op Runtime.Ordo Limbs
newLimbs = do
  x <- Obj.allocate Types.Kind.BUFFER
    (Types.Header.withPart Types.Header.BufferBytesP (8 * (1 + capacity)) Types.Header.noParts)
  setCount x 0
  Runtime.Ordo.pure x

||| The number set to a word.
export
setWord : Limbs -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo ()
setWord x v = if v == 0 then setCount x 0 else do
  Bignum.Run.setLimb (run x) 0 v
  setCount x 1

||| The number times `m`, plus `a`, its carry out of the top a new limb.
export covering
mulAdd : Limbs -> (m, a : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
mulAdd x m a = do
  n <- count x
  carry <- Bignum.Run.mulAdd (run x) (run x) n m a
  if carry == 0 then Runtime.Ordo.pure () else
    if n >= capacity
       then Runtime.Ordo.crashOp
         "Native.Support.Double.Limbs.mulAdd: a number of more limbs than it holds"
       else do
         Bignum.Run.setLimb (run x) n carry
         setCount x (n + 1)

||| The number times 5^k: by 5^27, the largest power of five in a word,
||| then by the rest.
export covering
mulPow5 : Limbs -> (k : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
mulPow5 x k =
  if k >= 27 then do
    mulAdd x 7450580596923828125 0
    mulPow5 x (k - 27)
  else if k == 0 then Runtime.Ordo.pure ()
  else mulAdd x (power k) 0
  where
    power : Bits64 -> Bits64
    power 0 = 1
    -- lint: allow trust-escape: j is positive here, so j - 1 is smaller
    power j = 5 * power (assert_smaller j (j - 1))

||| The number shifted left by `s` bits: its limbs moved up by `s / 64` and
||| shifted by the rest, zeros below them, the bits out of the top a new
||| limb.
export covering
shiftLeft : Limbs -> (s : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
shiftLeft x s = do
  n <- count x
  if n == 0 then Runtime.Ordo.pure () else do
    let words = s `shiftR` 6
        bits = s .&. 63
    if n + words + 1 > capacity
       then Runtime.Ordo.crashOp
         "Native.Support.Double.Limbs.shiftLeft: a number of more limbs than it holds"
       else do
         over <- Bignum.Run.shiftLeft (Bignum.Run.from (run x) words) (run x) n bits 0
         Bignum.Run.zero (run x) words
         if over == 0 then setCount x (n + words) else do
           Bignum.Run.setLimb (run x) (n + words) over
           setCount x (n + words + 1)

||| How two numbers compare: -1, 0 or 1. With no zero limb on top, the one
||| of more limbs is larger; of as many, their limbs compare.
export covering
compareLimbs : Limbs -> Limbs -> Runtime.Ordo.Op Runtime.Ordo Int
compareLimbs x y = do
  n <- count x
  m <- count y
  if n /= m then Runtime.Ordo.pure (if n < m then -1 else 1)
    else Bignum.Run.compare (run x) (run y) n
