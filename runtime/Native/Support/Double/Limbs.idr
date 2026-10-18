||| Natural numbers of up to 6144 bits in 64-bit limbs (`Limbs`), the few
||| operations that decide a decimal's double exactly need: setting one to a
||| word, multiplying by a word and adding one, multiplying by a power of
||| five, shifting left, and comparing. A number is a byte buffer: its
||| count of limbs in use at word 0, then its limbs from the lowest, with no
||| zero limb on top.
module Native.Support.Double.Limbs

-- lint: allow public-import: the flat translation reaches through this module
-- (checking an importer's flat functions, it reaches this module's bodies,
-- which use them, so they are loaded wherever this module is)
import public Native.Primitive.Mul128
import public Native.Support.Obj
-- lint: allow public-import: `Limbs` is an object of a kind, which an
-- importer's code reduces
import public Native.Types.Kind

import Native.HeapObj.Shape as HeapObj
import Native.Runtime.Bits
import Native.Runtime.Heap as Runtime
import Native.Runtime.Raw as Runtime
import Native.Runtime.Space
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
count : Limbs -> Runtime.Heap.Op Runtime.Heap Bits64
count x = Obj.load64 x 8

setCount : Limbs -> Bits64 -> Runtime.Heap.Op Runtime.Heap ()
setCount x n = Obj.store64 x 8 n

||| Limb `i`, and setting it.
limb : Limbs -> (i : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
limb x i = Obj.load64 x (16 + 8 * i)

setLimb : Limbs -> (i, v : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
setLimb x i v = Obj.store64 x (16 + 8 * i) v

||| A new number, zero.
export
newLimbs : Runtime.Heap.Op Runtime.Heap Limbs
newLimbs = do
  let bytes = 8 * (1 + capacity)
      header = Types.Header.fixedWord Types.Kind.BUFFER + Types.Header.partBits Types.Header.BufferBytes bytes
  a <- Runtime.Space.allocate (8 * HeapObj.Shape.objectWordsOf header)
  let x = Obj.objectAt {k = Types.Kind.BUFFER} a
  Obj.store64 x 0 header
  setCount x 0
  Runtime.Heap.pure x

||| The number set to a word.
export
setWord : Limbs -> Bits64 -> Runtime.Heap.Op Runtime.Heap ()
setWord x v = if v == 0 then setCount x 0 else do
  setLimb x 0 v
  setCount x 1

||| The number times `m`, plus `a`: each limb's product with the carry
||| below added, its high word the carry above.
export covering
mulAdd : Limbs -> (m, a : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
mulAdd x m a = do
  n <- count x
  carry <- go 0 n a
  if carry == 0 then Runtime.Heap.pure () else
    if n >= capacity
       then Runtime.Heap.crashOp "Native.Support.Double.Limbs.mulAdd: a number of more limbs than it holds"
       else do
         setLimb x n carry
         setCount x (n + 1)
  where
    covering
    go : (i, n, carry : Bits64) -> Runtime.Heap.Op Runtime.Heap Bits64
    go i n carry = if i >= n then Runtime.Heap.pure carry else do
      v <- limb x i
      case mul128 v m of
        (h, l) => do
          let l' = l + carry
          setLimb x i l'
          go (i + 1) n (if l' < l then h + 1 else h)

||| The number times 5^k: by 5^27, the largest power of five in a word,
||| then by the rest.
export covering
mulPow5 : Limbs -> (k : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
mulPow5 x k =
  if k >= 27 then do
    mulAdd x 7450580596923828125 0
    mulPow5 x (k - 27)
  else if k == 0 then Runtime.Heap.pure ()
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
shiftLeft : Limbs -> (s : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
shiftLeft x s = do
  n <- count x
  if n == 0 then Runtime.Heap.pure () else do
    let words = s `shiftR` 6
        bits = s .&. 63
    if n + words + 1 > capacity
       then Runtime.Heap.crashOp "Native.Support.Double.Limbs.shiftLeft: a number of more limbs than it holds"
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
    moveUp : (i, words, bits : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
    moveUp i words bits = do
      v <- limb x i
      below <- if i == 0 then Runtime.Heap.pure 0 else limb x (i - 1)
      setLimb x (i + words) (if bits == 0 then v else (v `shiftL` bits) .|. (below `shiftR` (64 - bits)))
      if i == 0 then Runtime.Heap.pure () else moveUp (i - 1) words bits

    covering
    zeros : (i, words : Bits64) -> Runtime.Heap.Op Runtime.Heap ()
    zeros i words = if i >= words then Runtime.Heap.pure () else do
      setLimb x i 0
      zeros (i + 1) words

||| How two numbers compare: -1, 0 or 1. With no zero limb on top, the one
||| of more limbs is larger; of as many, the first limb from the top that
||| differs says.
export covering
compareLimbs : Limbs -> Limbs -> Runtime.Heap.Op Runtime.Heap Int
compareLimbs x y = do
  n <- count x
  m <- count y
  if n /= m then Runtime.Heap.pure (if n < m then -1 else 1) else go n
  where
    covering
    go : Bits64 -> Runtime.Heap.Op Runtime.Heap Int
    go 0 = Runtime.Heap.pure 0
    go i = do
      a <- limb x (i - 1)
      b <- limb y (i - 1)
      if a /= b then Runtime.Heap.pure (if a < b then -1 else 1) else go (i - 1)
