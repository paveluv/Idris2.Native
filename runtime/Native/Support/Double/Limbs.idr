||| Natural numbers of up to 6144 bits in 64-bit limbs (`Limbs`), the few
||| operations that decide a decimal's double exactly need: setting one to a
||| word, multiplying by a word and adding one, multiplying by a power of
||| five, shifting left, and comparing. A number is a byte buffer: its
||| count of limbs in use at word 0, then its limbs from the lowest, with no
||| zero limb on top.
module Native.Support.Double.Limbs

-- lint: allow public-import: `Limbs` is an object of a kind, which an
-- importer's code reduces
import public Native.Types.Kind

import Native.HeapObj.Shape as HeapObj
import Native.Primitive.Mul128
import Native.Runtime.Bits
import Native.Runtime.Ordo as Runtime
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

||| Limb `i`, and setting it.
limb : Limbs -> (i : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
limb x i = Obj.load64 x (8 + 8 * i)

setLimb : Limbs -> (i, v : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
setLimb x i v = Obj.store64 x (8 + 8 * i) v

||| A new number, zero.
export
newLimbs : Runtime.Ordo.Op Runtime.Ordo Limbs
newLimbs = do
  x <- Obj.allocate Types.Kind.BUFFER (Types.Header.withPart Types.Header.BufferBytes (8 * (1 + capacity)) Types.Header.noParts)
  setCount x 0
  Runtime.Ordo.pure x

||| The number set to a word.
export
setWord : Limbs -> Bits64 -> Runtime.Ordo.Op Runtime.Ordo ()
setWord x v = if v == 0 then setCount x 0 else do
  setLimb x 0 v
  setCount x 1

||| The number times `m`, plus `a`: each limb's product with the carry
||| below added, its high word the carry above.
export covering
mulAdd : Limbs -> (m, a : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
mulAdd x m a = do
  n <- count x
  carry <- go 0 n a
  if carry == 0 then Runtime.Ordo.pure () else
    if n >= capacity
       then Runtime.Ordo.crashOp "Native.Support.Double.Limbs.mulAdd: a number of more limbs than it holds"
       else do
         setLimb x n carry
         setCount x (n + 1)
  where
    covering
    go : (i, n, carry : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i n carry = if i >= n then Runtime.Ordo.pure carry else do
      v <- limb x i
      case mul128 v m of
        (h, l) => do
          let l' = l + carry
          setLimb x i l'
          go (i + 1) n (if l' < l then h + 1 else h)

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

||| The number shifted left by `s` bits: its limbs moved up by `s / 64`,
||| zeros below them, then shifted by the rest, each limb taking the bits
||| the one below loses.
export covering
shiftLeft : Limbs -> (s : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
shiftLeft x s = do
  n <- count x
  if n == 0 then Runtime.Ordo.pure () else do
    let words = s `shiftR` 6
        bits = s .&. 63
    if n + words + 1 > capacity
       then Runtime.Ordo.crashOp "Native.Support.Double.Limbs.shiftLeft: a number of more limbs than it holds"
       else do
         top <- limb x (n - 1)
         let over = if bits == 0 then 0 else top `shiftR` (64 - bits)
         moveUp (n - 1) words bits
         zeros 0 words
         if over == 0 then setCount x (n + words) else do
           setLimb x (n + words) over
           setCount x (n + words + 1)
  where
    -- limb i to i + words, shifted, from the top down, each with the bits
    -- the one below loses
    covering
    moveUp : (i, words, bits : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
    moveUp i words bits = do
      v <- limb x i
      below <- if i == 0 then Runtime.Ordo.pure 0 else limb x (i - 1)
      setLimb x (i + words) (if bits == 0 then v else (v `shiftL` bits) .|. (below `shiftR` (64 - bits)))
      if i == 0 then Runtime.Ordo.pure () else moveUp (i - 1) words bits

    covering
    zeros : (i, words : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
    zeros i words = if i >= words then Runtime.Ordo.pure () else do
      setLimb x i 0
      zeros (i + 1) words

||| How two numbers compare: -1, 0 or 1. With no zero limb on top, the one
||| of more limbs is larger; of as many, the first limb from the top that
||| differs says.
export covering
compareLimbs : Limbs -> Limbs -> Runtime.Ordo.Op Runtime.Ordo Int
compareLimbs x y = do
  n <- count x
  m <- count y
  if n /= m then Runtime.Ordo.pure (if n < m then -1 else 1) else go n
  where
    covering
    go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Int
    go 0 = Runtime.Ordo.pure 0
    go i = do
      a <- limb x (i - 1)
      b <- limb y (i - 1)
      if a /= b then Runtime.Ordo.pure (if a < b then -1 else 1) else go (i - 1)
