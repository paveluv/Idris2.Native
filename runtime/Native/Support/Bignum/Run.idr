||| Runs of 64-bit limbs (`Run`): a natural number's digits in base 2^64,
||| least significant first, a word each, from a byte offset into an
||| object's payload, and the operations on them every number of limbs is
||| made of: a limb read and written, a run times a word plus a word, or
||| added to another or subtracted from it, two runs added or subtracted
||| with a carry, a word carried or borrowed through a run, a run shifted by
||| fewer bits than a limb, two runs compared, and a run set to zero.
|||
||| A run knows where its limbs are, not how many: each operation is given
||| the count, so that it works on a whole number, a part of one, or a
||| number being made, of a `BIGNUM` or of a buffer of scratch limbs alike.
||| The operations that write a run may write the run they read, in place,
||| as each says.
module Native.Support.Bignum.Run

-- lint: allow public-import: a run's object is of a kind, whose raw shape
-- its operations ask, which an importer's code reduces
import public Native.Types.Kind as Types

import Native.HeapObj.Shape as HeapObj
import Native.Primitive.Mul128
import Native.Runtime.Bits
import Native.Runtime.Ordo as Runtime
import Native.Support.Obj

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The limbs of an object of a raw kind from the byte offset into its
||| payload.
public export
record Run (0 k : Types.Kind) where
  constructor MkRun
  obj : Obj k
  offset : Bits64

||| The run from its limb `i` on.
export %inline
from : Run k -> (i : Bits64) -> Run k
from r i = MkRun r.obj (r.offset + 8 * i)

||| Limb `i` of the run, and setting it.
export %inline
limb : {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} -> Run k -> (i : Bits64) ->
       Runtime.Ordo.Op Runtime.Ordo Bits64
limb r i = Obj.load64 r.obj (r.offset + 8 * i)

export %inline
setLimb : {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} -> Run k ->
          (i, v : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
setLimb r i v = Obj.store64 r.obj (r.offset + 8 * i) v

||| `n` limbs of `src` times `m`, plus `carry`, written to `dst`: each
||| limb's product with the carry below added, its high word the carry
||| above; the carry out of the top. `dst` may be `src`.
export covering
mulAdd : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
         {auto 0 rs : Types.Kind.shape k' = Just HeapObj.Shape.RAW} ->
         (dst : Run k) -> (src : Run k') -> (n, m, carry : Bits64) ->
         Runtime.Ordo.Op Runtime.Ordo Bits64
mulAdd dst src n m carry = go 0 carry
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      v <- limb src i
      case Primitive.Mul128.mul128 v m of
        (h, l) => do
          let l' = l + c
          setLimb dst i l'
          go (i + 1) (if l' < l then h + 1 else h)

||| `n` limbs of `src` times `m` added to `n` limbs of `dst`: each limb's
||| product, with the carry below and the limb it adds to, its high word
||| and the additions' carries the carry above; the carry out of the top,
||| which a product and two words below 2^64 keep in a word.
export covering
addMul : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
         {auto 0 rs : Types.Kind.shape k' = Just HeapObj.Shape.RAW} ->
         (dst : Run k) -> (src : Run k') -> (n, m : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
addMul dst src n m = go 0 0
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      v <- limb src i
      d <- limb dst i
      case Primitive.Mul128.mul128 v m of
        (h, l) => do
          let l' = l + c
              h' = if l' < l then h + 1 else h
              t = d + l'
          setLimb dst i t
          go (i + 1) (if t < d then h' + 1 else h')

||| `n` limbs of `src` times `m` subtracted from `n` limbs of `dst`, as
||| `addMul` adds them; the borrow out of the top, the word the next limb up
||| is to lose.
export covering
subMul : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
         {auto 0 rs : Types.Kind.shape k' = Just HeapObj.Shape.RAW} ->
         (dst : Run k) -> (src : Run k') -> (n, m : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
subMul dst src n m = go 0 0
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      v <- limb src i
      d <- limb dst i
      case Primitive.Mul128.mul128 v m of
        (h, l) => do
          let l' = l + c
              h' = if l' < l then h + 1 else h
          setLimb dst i (d - l')
          go (i + 1) (if d < l' then h' + 1 else h')

||| `n` limbs of `a` plus `n` of `b`, plus `carry`, 0 or 1, written to
||| `dst`; the carry out of the top. `dst` may be `a` or `b`.
export covering
add : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
      {auto 0 ra : Types.Kind.shape ka = Just HeapObj.Shape.RAW} ->
      {auto 0 rb : Types.Kind.shape kb = Just HeapObj.Shape.RAW} ->
      (dst : Run k) -> (a : Run ka) -> (b : Run kb) -> (n, carry : Bits64) ->
      Runtime.Ordo.Op Runtime.Ordo Bits64
add dst a b n carry = go 0 carry
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      x <- limb a i
      y <- limb b i
      let s = x + y
          t = s + c
      setLimb dst i t
      -- a carry out of either addition, which cannot both carry
      go (i + 1) (if s < x || t < s then 1 else 0)

||| `n` limbs of `a` minus `n` of `b`, minus `borrow`, 0 or 1, written to
||| `dst`; the borrow out of the top. `dst` may be `a` or `b`.
export covering
sub : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
      {auto 0 ra : Types.Kind.shape ka = Just HeapObj.Shape.RAW} ->
      {auto 0 rb : Types.Kind.shape kb = Just HeapObj.Shape.RAW} ->
      (dst : Run k) -> (a : Run ka) -> (b : Run kb) -> (n, borrow : Bits64) ->
      Runtime.Ordo.Op Runtime.Ordo Bits64
sub dst a b n borrow = go 0 borrow
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      x <- limb a i
      y <- limb b i
      let d = x - y
          e = d - c
      setLimb dst i e
      -- a borrow out of either subtraction, which cannot both borrow
      go (i + 1) (if x < y || d < c then 1 else 0)

||| `n` limbs of `a` plus `carry`, written to `dst`; the carry out of the
||| top. `dst` may be `a`. A carry stops at the first limb it does not
||| overflow, though the limbs above are still copied, as `dst` may not be
||| `a`.
export covering
addWord : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
          {auto 0 ra : Types.Kind.shape ka = Just HeapObj.Shape.RAW} ->
          (dst : Run k) -> (a : Run ka) -> (n, carry : Bits64) ->
          Runtime.Ordo.Op Runtime.Ordo Bits64
addWord dst a n carry = go 0 carry
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      x <- limb a i
      let t = x + c
      setLimb dst i t
      go (i + 1) (if t < x then 1 else 0)

||| `n` limbs of `a` minus `borrow`, written to `dst`; the borrow out of
||| the top. `dst` may be `a`.
export covering
subWord : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
          {auto 0 ra : Types.Kind.shape ka = Just HeapObj.Shape.RAW} ->
          (dst : Run k) -> (a : Run ka) -> (n, borrow : Bits64) ->
          Runtime.Ordo.Op Runtime.Ordo Bits64
subWord dst a n borrow = go 0 borrow
  where
    covering
    go : (i, c : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i c = if i >= n then Runtime.Ordo.pure c else do
      x <- limb a i
      setLimb dst i (x - c)
      go (i + 1) (if x < c then 1 else 0)

||| `n` limbs of `src` shifted left by `bits`, from 0 to 63, with the bits
||| `inBits` holds below them coming in at the bottom (the top bits of the
||| limb under the run), written to `dst`; the bits shifted out of the top,
||| in the low end of the word. From the top down, so that `dst` may be
||| `src` or above it in one object. A shift by 0 moves the limbs, as no
||| shift of a word by 64 bits gives 0 on every machine.
export covering
shiftLeft : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
            {auto 0 rs : Types.Kind.shape k' = Just HeapObj.Shape.RAW} ->
            (dst : Run k) -> (src : Run k') -> (n, bits, inBits : Bits64) ->
            Runtime.Ordo.Op Runtime.Ordo Bits64
shiftLeft dst src n bits inBits =
  if n == 0 then Runtime.Ordo.pure (out inBits) else do
    top <- limb src (n - 1)
    go (n - 1) top
    Runtime.Ordo.pure (out top)
  where
    -- the bits a limb loses at the top
    out : Bits64 -> Bits64
    out v = if bits == 0 then 0 else v `shiftR` (64 - bits)

    -- limb i, which is `v`, shifted, with the bits limb i - 1 loses
    covering
    go : (i, v : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
    go i v = do
      below <- if i == 0 then Runtime.Ordo.pure inBits else limb src (i - 1)
      setLimb dst i ((v `shiftL` bits) .|. out below)
      if i == 0 then Runtime.Ordo.pure () else go (i - 1) below

||| `n` limbs of `src` shifted right by `bits`, from 0 to 63, with the bits
||| of `inBits` coming in at the top (the low bits of the limb above the
||| run), written to `dst`; the bits shifted out of the bottom, in the high
||| end of the word. From the bottom up, so that `dst` may be `src` or below
||| it in one object. A shift by 0 moves the limbs, as `shiftLeft`'s does.
export covering
shiftRight : {auto 0 rd : Types.Kind.shape k = Just HeapObj.Shape.RAW} ->
             {auto 0 rs : Types.Kind.shape k' = Just HeapObj.Shape.RAW} ->
             (dst : Run k) -> (src : Run k') -> (n, bits, inBits : Bits64) ->
             Runtime.Ordo.Op Runtime.Ordo Bits64
shiftRight dst src n bits inBits =
  if n == 0 then Runtime.Ordo.pure (out inBits) else do
    bottom <- limb src 0
    go 0 bottom
    Runtime.Ordo.pure (out bottom)
  where
    -- the bits a limb loses at the bottom
    out : Bits64 -> Bits64
    out v = if bits == 0 then 0 else v `shiftL` (64 - bits)

    -- limb i, which is `v`, shifted, with the bits limb i + 1 loses
    covering
    go : (i, v : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
    go i v = do
      above <- if i + 1 >= n then Runtime.Ordo.pure inBits else limb src (i + 1)
      setLimb dst i ((v `shiftR` bits) .|. out above)
      if i + 1 >= n then Runtime.Ordo.pure () else go (i + 1) above

||| How `n` limbs of `a` compare with `n` of `b`, as numbers: -1, 0 or 1,
||| the first limb from the top that differs saying.
export covering
compare : {auto 0 ra : Types.Kind.shape ka = Just HeapObj.Shape.RAW} ->
          {auto 0 rb : Types.Kind.shape kb = Just HeapObj.Shape.RAW} ->
          (a : Run ka) -> (b : Run kb) -> (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Int
compare a b n = go n
  where
    covering
    go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo Int
    go 0 = Runtime.Ordo.pure 0
    go i = do
      x <- limb a (i - 1)
      y <- limb b (i - 1)
      if x /= y then Runtime.Ordo.pure (if x < y then -1 else 1) else go (i - 1)

||| `n` limbs of the run set to zero.
export covering
zero : {auto 0 raw : Types.Kind.shape k = Just HeapObj.Shape.RAW} -> Run k -> (n : Bits64) ->
       Runtime.Ordo.Op Runtime.Ordo ()
zero r n = go 0
  where
    covering
    go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo ()
    go i = if i >= n then Runtime.Ordo.pure () else do
      setLimb r i 0
      go (i + 1)
