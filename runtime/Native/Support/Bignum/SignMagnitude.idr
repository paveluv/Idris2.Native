||| `Integer`s beyond the fixnums under 64-bit limbs in sign-magnitude: the
||| one module of the runtime that reads a `BIGNUM`'s limbs. Every other part
||| of the runtime, and generated code, reaches one through these functions,
||| which the native code generator binds when a program's integers are so
||| laid out (`Types.IntegerRoutine`).
|||
||| A `BIGNUM` is a header word, its sign and its count of words, then its
||| magnitude's limbs, least significant first, its top limb never zero. An
||| `Integer` in the fixnum range, from -2^62 to 2^62 - 1, is a fixnum, and
||| one outside it a `BIGNUM`, never the other way round: so the routines
||| take an integer apart into its sign and its magnitude (`Magnitude`), a
||| fixnum's in a limb of its own, compute into an object of their own, and
||| give the canonical integer of what they computed (`result`).
|||
||| The operations mean what Idris's do, which the Chez backend gives: the
||| arithmetic exact; division and remainder Euclidean, the remainder from 0
||| to the divisor's magnitude, and a division by zero the end of the
||| program; the bitwise operations on the infinite two's-complement form,
||| negatives included; shifts arithmetic, a right shift flooring.
module Native.Support.Bignum.SignMagnitude

import Native.Support.Bignum.Run

import Native.Field
import Native.Flat.Uniform as Flat
import Native.HeapObj.Shape as HeapObj
import Native.Port
import Native.Primitive
import Native.Primitive.Div128
import Native.Primitive.DoubleBits
import Native.Primitive.Mul128
import Native.Runtime.Bits
import Native.Runtime.ByteAddr as Runtime
import Native.Runtime.Memory as Runtime
import Native.Runtime.Ordo as Runtime
import Native.Runtime.PortTy as Runtime
import Native.Support.Obj
import Native.Support.Text
import Native.Types.Header
import Native.Types.IntegerRoutine
import Native.Types.Kind
import Native.Types.Repr

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

------------------------------------------------------------------------------
-- The layout

||| A `BIGNUM`'s limbs, from the first word after its header.
limbs : Obj Types.Kind.BIGNUM -> Run Types.Kind.BIGNUM
limbs o = MkRun o 0

||| A header's parts: the sign and the words of the limbs.
partsFor : (negative : Bool) -> (words : Bits64) -> Types.Header.Parts Types.Kind.BIGNUM
partsFor neg n =
  Types.Header.withPart Types.Header.BignumNegative (if neg then 1 else 0)
    (Types.Header.withPart Types.Header.BignumWords n Types.Header.noParts)

||| A new `BIGNUM` of the sign and `n` words, its limbs still to be written
||| but the last, which is zero.
newBig : (negative : Bool) -> (n : Bits64) ->
         Runtime.Ordo.Op Runtime.Ordo (Obj Types.Kind.BIGNUM)
newBig neg n = Obj.allocate Types.Kind.BIGNUM (partsFor neg n)

||| An integer's sign and its magnitude: `count` limbs of the run, with no
||| zero on top, none for zero, which is never negative.
record Magnitude where
  constructor MkMagnitude
  negative : Bool
  count : Bits64
  run : Run Types.Kind.BIGNUM

||| An integer as it is held: a fixnum, or a `BIGNUM`'s magnitude.
data Taken = Small Int64 | Large Magnitude

||| The integer as it is held.
take : Flat.Uniform Integer -> Runtime.Ordo.Op Runtime.Ordo Taken
take v = do
  f <- Obj.valueFixnum v
  case f of
    Just n => Runtime.Ordo.pure (Small n)
    Nothing => do
      o <- Obj.asKind Types.Kind.BIGNUM v
      case o of
        Just b => do
          h <- Obj.header b
          Runtime.Ordo.pure
            (Large (MkMagnitude (Types.Header.readPart Types.Header.BignumNegative h == 1)
                     (Types.Header.readPart Types.Header.BignumWords h) (limbs b)))
        Nothing => Runtime.Ordo.crashOp "idris: an Integer that is neither a fixnum nor a BIGNUM"

||| A fixnum's sign and magnitude, its limb in an object of its own.
smallMagnitude : Int64 -> Runtime.Ordo.Op Runtime.Ordo Magnitude
smallMagnitude n = do
  o <- newBig False 1
  let m : Bits64 = if n < 0 then 0 - cast n else cast n
  Run.setLimb (limbs o) 0 m
  Runtime.Ordo.pure (MkMagnitude (n < 0) (if m == 0 then 0 else 1) (limbs o))

||| The integer's sign and magnitude.
magnitude : Flat.Uniform Integer -> Runtime.Ordo.Op Runtime.Ordo Magnitude
magnitude v = do
  t <- take v
  case t of
    Small n => smallMagnitude n
    Large m => Runtime.Ordo.pure m

||| How many of the first `n` limbs of the run count: `n` but the zeros on
||| top.
covering
significant : Run Types.Kind.BIGNUM -> (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
significant r n = if n == 0 then Runtime.Ordo.pure 0 else do
  l <- Run.limb r (n - 1)
  if l /= 0 then Runtime.Ordo.pure n else significant r (n - 1)

||| The canonical integer of the sign and the first `n` limbs of `r`, an
||| object the routine made, which may become the integer: a fixnum where
||| it is in the fixnum range, and else a `BIGNUM` of its limbs that count,
||| the object itself where it has as many words.
covering
result : (negative : Bool) -> Run Types.Kind.BIGNUM -> (n : Bits64) ->
         Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Integer)
result neg r n = do
  m <- significant r n
  if m == 0 then Obj.fixnumValue 0 else do
    l <- Run.limb r 0
    if m == 1 && (l < 0x4000000000000000 || (neg && l == 0x4000000000000000))
      then Obj.fixnumValue (if neg then 0 - cast l else cast l)
      else do
        h <- Obj.header r.obj
        if r.offset == 0 && Types.Header.readPart Types.Header.BignumWords h == m
          then do
            Obj.setHeader r.obj (partsFor neg m)
            Obj.objectValue r.obj
          else do
            o <- newBig neg m
            _ <- Run.shiftLeft (limbs o) r m 0 0
            Obj.objectValue o

------------------------------------------------------------------------------
-- Magnitudes

||| How two magnitudes compare: -1, 0 or 1.
covering
compareMagnitudes : Magnitude -> Magnitude -> Runtime.Ordo.Op Runtime.Ordo Int
compareMagnitudes a b =
  if a.count /= b.count then Runtime.Ordo.pure (if a.count < b.count then -1 else 1)
  else Run.compare a.run b.run a.count

||| The integer of the sign and the sum of the magnitudes.
covering
addMagnitudes : (negative : Bool) -> Magnitude -> Magnitude ->
                Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Integer)
addMagnitudes neg a b = do
  let l = if a.count >= b.count then a else b
      s = if a.count >= b.count then b else a
  r <- newBig neg (l.count + 1)
  c <- Run.add (limbs r) l.run s.run s.count 0
  c' <- Run.addWord (Run.from (limbs r) s.count) (Run.from l.run s.count)
          (l.count - s.count) c
  Run.setLimb (limbs r) l.count c'
  result neg (limbs r) (l.count + 1)

||| The integer of the sign and the difference of the magnitudes, the first
||| the larger.
covering
subMagnitudes : (negative : Bool) -> (larger, smaller : Magnitude) ->
                Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Integer)
subMagnitudes neg l s = do
  r <- newBig neg l.count
  b <- Run.sub (limbs r) l.run s.run s.count 0
  _ <- Run.subWord (Run.from (limbs r) s.count) (Run.from l.run s.count)
         (l.count - s.count) b
  result neg (limbs r) l.count

||| The sum of two integers by their signs and magnitudes.
covering
signedAdd : Magnitude -> Magnitude -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Integer)
signedAdd a b =
  if a.negative == b.negative then addMagnitudes a.negative a b else do
    c <- compareMagnitudes a b
    if c == 0 then Obj.fixnumValue 0
      else if c > 0 then subMagnitudes a.negative a b
      else subMagnitudes b.negative b a

------------------------------------------------------------------------------
-- Division

||| The places of a word's top bit from the top: the zeros above it, of a
||| word not zero.
leadingZeros : Bits64 -> Bits64
leadingZeros w =
  let (z1, w1) = step 32 0 w
      (z2, w2) = step 16 z1 w1
      (z3, w3) = step 8 z2 w2
      (z4, w4) = step 4 z3 w3
      (z5, w5) = step 2 z4 w4
      (z6, w6) = step 1 z5 w5
  in z6
  where
    -- a word whose top `k` bits are zero, shifted up past them
    step : (k, zeros, v : Bits64) -> (Bits64, Bits64)
    step k zeros v = if v `shiftR` (64 - k) == 0 then (zeros + k, v `shiftL` k) else (zeros, v)

||| `n` limbs of `src` divided by a word that is not zero, from the top, the
||| quotient's limbs written to `dst`, which may be `src`: the remainder.
||| Each digit's high word is the remainder of the digit above, below the
||| divisor as the division ensures, and the first's is zero, below the
||| divisor as it is not zero: no digit asks.
covering
divideInto : (dst, src : Run Types.Kind.BIGNUM) -> (n, d : Bits64) ->
             (0 nonzero : (0 < d) = True) -> Runtime.Ordo.Op Runtime.Ordo Bits64
divideInto dst src n d nonzero = go n 0 nonzero
  where
    covering
    go : (i, rem : Bits64) -> (0 below : (rem < d) = True) -> Runtime.Ordo.Op Runtime.Ordo Bits64
    go i rem below = if i == 0 then Runtime.Ordo.pure rem else do
      x <- Run.limb src (i - 1)
      case Primitive.Div128.div128 rem x d below of
        Primitive.MkProven (q, r') next => do
          Run.setLimb dst (i - 1) q
          go (i - 1) r' next

||| A long division's estimate of a quotient digit, from the top two limbs
||| of what is left and the divisor's top limb: their quotient and remainder
||| where the high word is below the divisor's limb, which the comparison
||| proves; else the largest digit, and the remainder it leaves, which may
||| carry past a word, as the third says.
estimate : (high, low, top : Bits64) -> (Bits64, Bits64, Bool)
estimate high low top with (high < top) proof below
  _ | True = case Primitive.Div128.div128 high low top below of
               Primitive.MkProven (q, r) _ => (q, r, False)
  _ | False = let r = low + top in (0xFFFFFFFFFFFFFFFF, r, r < low)

||| A division of magnitudes, truncated: the quotient's limbs, `qcount` of
||| them, in an object with a word more, which a quotient made one larger
||| needs, and the remainder's, `rcount` of them; both objects the
||| routine's own.
record Division where
  constructor MkDivision
  quotient : Run Types.Kind.BIGNUM
  qcount : Bits64
  remainder : Run Types.Kind.BIGNUM
  rcount : Bits64

||| The magnitudes divided, the divisor not zero.
covering
divide : Magnitude -> Magnitude -> Runtime.Ordo.Op Runtime.Ordo Division
divide a b = if b.count == 0 then Runtime.Ordo.crashOp "idris: an Integer divided by zero" else do
  c <- compareMagnitudes a b
  if c >= 0 then (if b.count == 1 then byLimb else knuth) else do
    q <- newBig False 1
    r <- newBig False (if a.count == 0 then 1 else a.count)
    _ <- Run.shiftLeft (limbs r) a.run a.count 0 0
    Runtime.Ordo.pure (MkDivision (limbs q) 0 (limbs r) a.count)
  where
    -- by one limb, a magnitude's top limb, which is not zero: the program
    -- ends for a BIGNUM that breaks that, which no routine makes
    covering
    byLimb : Runtime.Ordo.Op Runtime.Ordo Division
    byLimb = do
      d <- Run.limb b.run 0
      q <- newBig False (a.count + 1)
      rem <- byWord (limbs q) d
      r <- newBig False 1
      Run.setLimb (limbs r) 0 rem
      Runtime.Ordo.pure (MkDivision (limbs q) a.count (limbs r) 1)
      where
        covering
        byWord : Run Types.Kind.BIGNUM -> (d : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bits64
        byWord q d with (0 < d) proof nonzero
          _ | True = divideInto q a.run a.count d nonzero
          _ | False = Runtime.Ordo.crashOp "idris: a BIGNUM whose top limb is zero"

    -- Knuth's algorithm D: the divisor shifted so that its top limb's top
    -- bit is set, the dividend shifted as far, a limb more on top; each
    -- quotient digit estimated from the top two limbs of the part of the
    -- dividend left over the divisor's top limb, corrected by the next,
    -- which leaves it at most one too large, and that one taken back where
    -- the subtraction of the divisor times it borrows
    covering
    knuth : Runtime.Ordo.Op Runtime.Ordo Division
    knuth = do
      let n = b.count
          m = a.count
      top <- Run.limb b.run (n - 1)
      let s = leadingZeros top
      bn <- newBig False n
      _ <- Run.shiftLeft (limbs bn) b.run n s 0
      an <- newBig False (m + 1)
      over <- Run.shiftLeft (limbs an) a.run m s 0
      Run.setLimb (limbs an) m over
      q <- newBig False (m - n + 2)
      d1 <- Run.limb (limbs bn) (n - 1)
      d2 <- Run.limb (limbs bn) (n - 2)
      steps (limbs an) (limbs bn) (limbs q) n d1 d2 (m - n + 1)
      r <- newBig False n
      rest <- Run.limb (limbs an) n
      _ <- Run.shiftRight (limbs r) (limbs an) n s rest
      Runtime.Ordo.pure (MkDivision (limbs q) (m - n + 1) (limbs r) n)
      where
        -- the estimate's correction: lower while its product with the
        -- divisor's second limb exceeds the remainder's two words and the
        -- dividend's next limb, as long as the remainder is a word
        covering
        correct : (d1, d2, qhat, rhat, next : Bits64) -> (carried : Bool) -> Bits64
        correct d1 d2 qhat rhat next carried =
          if carried then qhat else case Primitive.Mul128.mul128 qhat d2 of
            (ph, pl) =>
              if ph > rhat || (ph == rhat && pl > next)
                then let rhat' = rhat + d1 in correct d1 d2 (qhat - 1) rhat' next (rhat' < rhat)
                else qhat

        -- the digit at `j`, for j from the count of digits down to 0
        covering
        steps : (an, bn, q : Run Types.Kind.BIGNUM) -> (n, d1, d2, j : Bits64) ->
                Runtime.Ordo.Op Runtime.Ordo ()
        steps an bn q n d1 d2 j = if j == 0 then Runtime.Ordo.pure () else do
          let i = j - 1
          hi <- Run.limb an (i + n)
          lo <- Run.limb an (i + n - 1)
          next <- Run.limb an (i + n - 2)
          let (qhat, rhat, carried) = estimate hi lo d1
          let qhat' = correct d1 d2 qhat rhat next carried
          borrow <- Run.subMul (Run.from an i) bn n qhat'
          t <- Run.limb an (i + n)
          Run.setLimb an (i + n) (t - borrow)
          if t >= borrow then Run.setLimb q i qhat' else do
            c <- Run.add (Run.from an i) (Run.from an i) bn n 0
            t' <- Run.limb an (i + n)
            Run.setLimb an (i + n) (t' + c)
            Run.setLimb q i (qhat' - 1)
          steps an bn q n d1 d2 i

------------------------------------------------------------------------------
-- Two's complement

||| `n` limbs of the run complemented.
covering
complement : Run Types.Kind.BIGNUM -> (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
complement r n = go 0
  where
    covering
    go : Bits64 -> Runtime.Ordo.Op Runtime.Ordo ()
    go i = if i >= n then Runtime.Ordo.pure () else do
      v <- Run.limb r i
      Run.setLimb r i (0xFFFFFFFFFFFFFFFF - v)
      go (i + 1)

||| The magnitude's integer in two's complement, in `l` limbs, more than its
||| own, so that the top limb is all its sign: a negative's, the magnitude
||| less one, complemented.
covering
twos : Magnitude -> (l : Bits64) -> Runtime.Ordo.Op Runtime.Ordo (Run Types.Kind.BIGNUM)
twos a l = do
  t <- newBig False l
  if not a.negative
    then do
      _ <- Run.shiftLeft (limbs t) a.run a.count 0 0
      Run.zero (Run.from (limbs t) a.count) (l - a.count)
    else do
      _ <- Run.subWord (limbs t) a.run a.count 1
      Run.zero (Run.from (limbs t) a.count) (l - a.count)
      complement (limbs t) l
  Runtime.Ordo.pure (limbs t)

||| The integer of a bitwise operation on two integers, limb by limb on
||| their two's-complement forms, the result's top limb its sign.
covering
bitwise : (Bits64 -> Bits64 -> Bits64) -> Flat.Uniform Integer -> Flat.Uniform Integer ->
          Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Integer)
bitwise op x y = do
  a <- magnitude x
  b <- magnitude y
  let l = (if a.count >= b.count then a.count else b.count) + 1
  ta <- twos a l
  tb <- twos b l
  r <- newBig False l
  go ta tb (limbs r) l 0
  top <- Run.limb (limbs r) (l - 1)
  if top `shiftR` 63 == 0 then result False (limbs r) l else do
    complement (limbs r) l
    _ <- Run.addWord (limbs r) (limbs r) l 1
    result True (limbs r) l
  where
    covering
    go : (ta, tb, r : Run Types.Kind.BIGNUM) -> (l, i : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
    go ta tb r l i = if i >= l then Runtime.Ordo.pure () else do
      u <- Run.limb ta i
      v <- Run.limb tb i
      Run.setLimb r i (op u v)
      go ta tb r l (i + 1)

------------------------------------------------------------------------------
-- Shifts

||| A shift's count, if it is one memory could hold the result of: a
||| fixnum, not negative, which a count of a `Nat` always is.
shiftCount : Flat.Uniform Integer -> Runtime.Ordo.Op Runtime.Ordo (Maybe Bits64)
shiftCount k = do
  t <- take k
  case t of
    Small n => Runtime.Ordo.pure (if n < 0 then Nothing else Just (cast n))
    Large _ => Runtime.Ordo.pure Nothing

||| Whether any of the first `n` limbs of the run is not zero.
covering
anyLimb : Run Types.Kind.BIGNUM -> (n : Bits64) -> Runtime.Ordo.Op Runtime.Ordo Bool
anyLimb r n = if n == 0 then Runtime.Ordo.pure False else do
  v <- Run.limb r (n - 1)
  if v /= 0 then Runtime.Ordo.pure True else anyLimb r (n - 1)

------------------------------------------------------------------------------
-- The routines

%cg native flat Support.Bignum.SignMagnitude.add
||| The sum.
export covering
add : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Add)
add x y = do
  a <- magnitude x
  b <- magnitude y
  signedAdd a b

%cg native flat Support.Bignum.SignMagnitude.sub
||| The difference.
export covering
sub : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Sub)
sub x y = do
  a <- magnitude x
  b <- magnitude y
  signedAdd a ({ negative := not b.negative } b)

%cg native flat Support.Bignum.SignMagnitude.mul
||| The product, by schoolbook multiplication: each limb of the second
||| times the first, added in at its place.
export covering
mul : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Mul)
mul x y = do
  a <- magnitude x
  b <- magnitude y
  if a.count == 0 || b.count == 0 then Obj.fixnumValue 0 else do
    let n = a.count + b.count
    r <- newBig False n
    Run.zero (limbs r) n
    rows a b (limbs r) 0
    result (a.negative /= b.negative) (limbs r) n
  where
    covering
    rows : Magnitude -> Magnitude -> Run Types.Kind.BIGNUM -> Bits64 ->
           Runtime.Ordo.Op Runtime.Ordo ()
    rows a b r j = if j >= b.count then Runtime.Ordo.pure () else do
      v <- Run.limb b.run j
      c <- Run.addMul (Run.from r j) a.run a.count v
      Run.setLimb r (j + a.count) c
      rows a b r (j + 1)

%cg native flat Support.Bignum.SignMagnitude.div
||| The Euclidean quotient: truncated, then one further from zero where
||| the dividend is negative and the division is not exact, so that the
||| remainder is not negative.
export covering
div : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Div)
div x y = do
  a <- magnitude x
  b <- magnitude y
  d <- divide a b
  inexact <- anyLimb d.remainder d.rcount
  if not a.negative || not inexact then result (a.negative /= b.negative) d.quotient d.qcount
    else do
      c <- Run.addWord d.quotient d.quotient d.qcount 1
      Run.setLimb d.quotient d.qcount c
      result (not b.negative) d.quotient (d.qcount + 1)

%cg native flat Support.Bignum.SignMagnitude.mod
||| The Euclidean remainder: the truncated one, or the divisor's magnitude
||| less it where the dividend is negative and the division is not exact;
||| never negative.
export covering
mod : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Mod)
mod x y = do
  a <- magnitude x
  b <- magnitude y
  d <- divide a b
  inexact <- anyLimb d.remainder d.rcount
  if not a.negative || not inexact then result False d.remainder d.rcount else do
    t <- newBig False b.count
    borrow <- Run.sub (limbs t) b.run d.remainder d.rcount 0
    _ <- Run.subWord (Run.from (limbs t) d.rcount) (Run.from b.run d.rcount)
           (b.count - d.rcount) borrow
    result False (limbs t) b.count

%cg native flat Support.Bignum.SignMagnitude.and
||| The bitwise and, of the two's-complement forms.
export covering
and : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.And)
and x y = bitwise (\u, v => u .&. v) x y

%cg native flat Support.Bignum.SignMagnitude.or
||| The bitwise or.
export covering
or : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Or)
or x y = bitwise (\u, v => u .|. v) x y

%cg native flat Support.Bignum.SignMagnitude.xor
||| The bitwise exclusive or.
export covering
xor : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Xor)
xor x y = bitwise prim__xor_Bits64 x y

%cg native flat Support.Bignum.SignMagnitude.shl
||| The integer times 2 to the count: its limbs moved up by the count's
||| whole limbs and shifted by the rest. The program ends for a count
||| beyond what memory could hold.
export covering
shl : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Shl)
shl x k = do
  c <- shiftCount k
  case c of
    Nothing => Runtime.Ordo.crashOp "idris: an Integer shifted left beyond what memory holds"
    Just n => do
      a <- magnitude x
      if a.count == 0 then Obj.fixnumValue 0 else do
        let words = n `shiftR` 6
            bits = n .&. 63
        r <- newBig a.negative (a.count + words + 1)
        Run.zero (limbs r) words
        over <- Run.shiftLeft (Run.from (limbs r) words) a.run a.count bits 0
        Run.setLimb (limbs r) (a.count + words) over
        result a.negative (limbs r) (a.count + words + 1)

%cg native flat Support.Bignum.SignMagnitude.shr
||| The integer divided by 2 to the count, floored: its magnitude shifted
||| down, and a negative's one further from zero where a bit it lost was
||| set; past its limbs, 0, or -1 for a negative.
export covering
shr : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Shr)
shr x k = do
  a <- magnitude x
  c <- shiftCount k
  case c of
    Nothing => gone a.negative
    Just n => do
      let words = n `shiftR` 6
          bits = n .&. 63
      if words >= a.count then gone a.negative else do
        let cnt = a.count - words
        r <- newBig a.negative (cnt + 1)
        out <- Run.shiftRight (limbs r) (Run.from a.run words) cnt bits 0
        Run.setLimb (limbs r) cnt 0
        lostBelow <- anyLimb a.run words
        if not a.negative || (out == 0 && not lostBelow) then result a.negative (limbs r) cnt
          else do
            _ <- Run.addWord (limbs r) (limbs r) (cnt + 1) 1
            result True (limbs r) (cnt + 1)
  where
    -- every limb shifted out: 0, or -1 for a negative
    gone : Bool -> Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform Integer)
    gone negative = Obj.fixnumValue (if negative then -1 else 0)

%cg native flat Support.Bignum.SignMagnitude.neg
||| The integer negated: a `BIGNUM`'s limbs under the other sign, and a
||| fixnum's negation, which is no fixnum for the least, -2^62.
export covering
neg : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Neg)
neg x = do
  t <- take x
  case t of
    Small n => do
      m <- smallMagnitude n
      result (not m.negative && m.count /= 0) m.run m.count
    Large m => do
      r <- newBig (not m.negative) m.count
      _ <- Run.shiftLeft (limbs r) m.run m.count 0 0
      Obj.objectValue r

%cg native flat Support.Bignum.SignMagnitude.compare
||| How two integers compare: -1, 0 or 1. A `BIGNUM`'s magnitude is beyond
||| every fixnum's, so its sign alone orders it against one.
export covering
compare : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.Compare)
compare x y = do
  s <- take x
  t <- take y
  case (s, t) of
    (Small a, Small b) => Runtime.Ordo.pure (if a < b then -1 else if a > b then 1 else 0)
    (Small _, Large b) => Runtime.Ordo.pure (if b.negative then 1 else -1)
    (Large a, Small _) => Runtime.Ordo.pure (if a.negative then -1 else 1)
    (Large a, Large b) =>
      if a.negative /= b.negative then Runtime.Ordo.pure (if a.negative then -1 else 1) else do
        c <- compareMagnitudes a b
        Runtime.Ordo.pure (if a.negative then 0 - c else c)

%cg native flat Support.Bignum.SignMagnitude.toBits64
||| The integer modulo 2^64: its lowest limb, negated for a negative.
export covering
toBits64 : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.ToBits64)
toBits64 x = do
  t <- take x
  case t of
    Small n => Runtime.Ordo.pure (cast n)
    Large m => do
      l <- Run.limb m.run 0
      Runtime.Ordo.pure (if m.negative then 0 - l else l)

%cg native flat Support.Bignum.SignMagnitude.fromInt64
||| The integer of a signed word: a fixnum, or a `BIGNUM` of one limb.
export covering
fromInt64 : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.FromInt64)
fromInt64 w =
  if w >= -4611686018427387904 && w <= 4611686018427387903 then Obj.fixnumValue (cast w) else do
    r <- newBig (w < 0) 1
    let m : Bits64 = if w < 0 then 0 - cast w else cast w
    Run.setLimb (limbs r) 0 m
    Obj.objectValue r

%cg native flat Support.Bignum.SignMagnitude.fromBits64
||| The integer of an unsigned word: a fixnum, or a `BIGNUM` of one limb.
export covering
fromBits64 : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.FromBits64)
fromBits64 w = if w < 0x4000000000000000 then Obj.fixnumValue (cast w) else do
  r <- newBig False 1
  Run.setLimb (limbs r) 0 w
  Obj.objectValue r

------------------------------------------------------------------------------
-- Decimal text

||| Ten to the 19th, the largest power of ten in a word: a decimal is
||| written and read 19 digits at a time.
chunk : Bits64
chunk = 10000000000000000000

||| How many decimal digits a word has, one for zero.
covering
digitsIn : Bits64 -> Bits64
digitsIn w = if w < 10 then 1 else 1 + digitsIn (Prelude.div w 10)

||| A word's `width` last decimal digits, zeros before them, as bytes of the
||| buffer ending before `end`.
covering
writeDigits : Obj Types.Kind.BUFFER -> (end, width, w : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
writeDigits b end width w = if width == 0 then Runtime.Ordo.pure () else do
  Obj.store8 b (end - 1) (48 + Prelude.mod w 10)
  writeDigits b (end - 1) (width - 1) (Prelude.div w 10)

%cg native flat Support.Bignum.SignMagnitude.toDecimal
||| The integer in decimal, `-` before a negative one's digits: its
||| magnitude divided by 10^19 until nothing is left, each remainder 19
||| digits but the last, the highest, written as many as it has.
export covering
toDecimal : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.ToDecimal)
toDecimal x = do
  a <- magnitude x
  t <- newBig False (if a.count == 0 then 1 else a.count)
  _ <- Run.shiftLeft (limbs t) a.run a.count 0 0
  -- a word holds 19.3 decimal digits, so a limb gives at most two chunks
  cs <- newBig False (2 * a.count + 1)
  k <- chunks (limbs t) (limbs cs) a.count 0
  top <- Run.limb (limbs cs) (k - 1)
  let sign : Bits64 = if a.negative then 1 else 0
      n = sign + digitsIn top + 19 * (k - 1)
  b <- Obj.allocate Types.Kind.BUFFER
         (Types.Header.withPart Types.Header.BufferBytes n Types.Header.noParts)
  if a.negative then Obj.store8 b 0 45 else Runtime.Ordo.pure ()
  write b (limbs cs) k n
  writeDigits b (sign + digitsIn top) (digitsIn top) top
  Text.ofText (Obj.objectBytes b 0) n
  where
    -- the chunks of `n` limbs of `t`, from the lowest, into `cs` from `k`:
    -- their count, one at least
    covering
    chunks : (t, cs : Run Types.Kind.BIGNUM) -> (n, k : Bits64) ->
             Runtime.Ordo.Op Runtime.Ordo Bits64
    chunks t cs n k = do
      rem <- divideInto t t n chunk Refl
      Run.setLimb cs k rem
      n' <- significant t n
      if n' == 0 then Runtime.Ordo.pure (k + 1) else chunks t cs n' (k + 1)

    -- the chunks below the highest, 19 digits each, from the end
    covering
    write : Obj Types.Kind.BUFFER -> Run Types.Kind.BIGNUM -> (k, end : Bits64) ->
            Runtime.Ordo.Op Runtime.Ordo ()
    write b cs k end = go 0 end
      where
        covering
        go : (i, e : Bits64) -> Runtime.Ordo.Op Runtime.Ordo ()
        go i e = if i + 1 >= k then Runtime.Ordo.pure () else do
          c <- Run.limb cs i
          writeDigits b e 19 c
          go (i + 1) (e - 19)

%cg native flat Support.Bignum.SignMagnitude.fromDecimal
||| The integer a string is: a sign, `+` or `-`, digits with at most one
||| point among them and at least one digit, its value the decimal's,
||| truncated toward zero, as `readWord` reads one, but whole; 0 for any
||| other text. The digits before the point are taken 19 at a time, each
||| run of them the number so far times a power of ten plus their word.
export covering
fromDecimal : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.FromDecimal)
fromDecimal s = Text.withText s (Obj.fixnumValue 0) (\p, n => do
  if n == 0 then Obj.fixnumValue 0 else do
    c0 <- Runtime.Memory.loadByteAt p 0
    let negative = c0 == 45
        start : Bits64 = if negative || c0 == 43 then 1 else 0
    -- the whole part's end, if the text is a decimal
    whole <- scan p n start start False False
    case whole of
      Nothing => Obj.fixnumValue 0
      Just e => do
        r <- newBig False (Prelude.div (e - start) 19 + 2)
        count <- accumulate p (limbs r) start e 0
        result negative (limbs r) count)
  where
    -- the end of the digits before the point, where the text from `i` is
    -- digits with at most one point and one digit at least
    covering
    scan : Runtime.ByteAddr -> (n, i, end : Bits64) -> (any, point : Bool) ->
           Runtime.Ordo.Op Runtime.Ordo (Maybe Bits64)
    scan p n i end any point =
      if i >= n then Runtime.Ordo.pure (if any then Just (if point then end else i) else Nothing)
        else do
        b <- Runtime.Memory.loadByteAt p i
        if b == 46 && not point then scan p n (i + 1) i any True
          else if b >= 48 && b <= 57 then scan p n (i + 1) end True point
          else Runtime.Ordo.pure Nothing

    -- the digits from `i` to `e` taken into the `count` limbs of `r`, up to
    -- 19 at a time: the new count
    covering
    accumulate : Runtime.ByteAddr -> Run Types.Kind.BIGNUM -> (i, e, count : Bits64) ->
                 Runtime.Ordo.Op Runtime.Ordo Bits64
    accumulate p r i e count = if i >= e then Runtime.Ordo.pure count else do
      let k = if e - i < 19 then e - i else 19
      (w, scale) <- word p i (i + k) 0 1
      carry <- Run.mulAdd r r count scale w
      if carry == 0 then accumulate p r (i + k) e count else do
        Run.setLimb r count carry
        accumulate p r (i + k) e (count + 1)
      where
        -- the digits from `j` to `f` as a word, and ten to their number
        covering
        word : Runtime.ByteAddr -> (j, f, v, t : Bits64) ->
               Runtime.Ordo.Op Runtime.Ordo (Bits64, Bits64)
        word p j f v t = if j >= f then Runtime.Ordo.pure (v, t) else do
          b <- Runtime.Memory.loadByteAt p j
          word p (j + 1) f (v * 10 + (b - 48)) (t * 10)

------------------------------------------------------------------------------
-- Doubles

%cg native flat Support.Bignum.SignMagnitude.toDouble
||| The double nearest the integer, ties to even, as IEEE 754 rounds: a
||| fixnum's by the machine's conversion; a `BIGNUM`'s from its top 64
||| significant bits and whether any bit below them is set, rounded to 53
||| bits, its exponent the place of its top bit; an infinity of its sign
||| from 2^1024 on.
export covering
toDouble : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.ToDouble)
toDouble x = do
  t <- take x
  case t of
    Small n => Runtime.Ordo.pure (cast n)
    Large m => do
      top <- Run.limb m.run (m.count - 1)
      next <- if m.count >= 2 then Run.limb m.run (m.count - 2) else Runtime.Ordo.pure 0
      below <- anyLimb m.run (if m.count >= 2 then m.count - 2 else 0)
      let z = leadingZeros top
          -- the top 64 significant bits, and those of `next` left out of them
          high = if z == 0 then top else (top `shiftL` z) .|. (next `shiftR` (64 - z))
          left = if z == 0 then next else next `shiftL` z
          sticky = left /= 0 || below
          q = high `shiftR` 11
          rest = high .&. 0x7FF
          up = rest > 0x400 || (rest == 0x400 && (sticky || q .&. 1 == 1))
          q' = if up then q + 1 else q
          -- the place of the top bit, one more where the rounding carried out
          place = 64 * m.count - z - 1 + (if q' == 0x20000000000000 then 1 else 0)
          sign : Bits64 = if m.negative then 0x8000000000000000 else 0
      Runtime.Ordo.pure (Primitive.DoubleBits.bitsDouble
        (if place > 1023 then sign .|. 0x7FF0000000000000
          else sign .|. ((place + 1023) `shiftL` 52) .|. (q' .&. 0xFFFFFFFFFFFFF)))

%cg native flat Support.Bignum.SignMagnitude.fromDouble
||| The integer of a double, its exact truncation toward zero, read from
||| its bits: 0 for NaN and the infinities, whose exponent field is all
||| ones, and for any double below 1; a fixnum below 2^62; else its
||| significand shifted up as its exponent says, in a `BIGNUM`.
export covering
fromDouble : Runtime.PortTy (Types.IntegerRoutine.port Types.IntegerRoutine.FromDouble)
fromDouble f = do
  let b = Primitive.DoubleBits.doubleBits f
      e = (b `shiftR` 52) .&. 0x7FF
      negative = b `shiftR` 63 == 1
      m = (b .&. 0xFFFFFFFFFFFFF) .|. 0x10000000000000
  if e == 0x7FF || e < 1023 then Obj.fixnumValue 0
    else if e < 1085 then do
      -- below 2^62: the significand shifted down past the point, or up
      let v = if e >= 1075 then m `shiftL` (e - 1075) else m `shiftR` (1075 - e)
      Obj.fixnumValue (if negative then 0 - cast v else cast v)
    else do
      let s = e - 1075
          words = s `shiftR` 6
          bits = s .&. 63
      r <- newBig negative (words + 2)
      Run.zero (limbs r) words
      Run.setLimb (limbs r) words (m `shiftL` bits)
      Run.setLimb (limbs r) (words + 1) (if bits == 0 then 0 else m `shiftR` (64 - bits))
      result negative (limbs r) (words + 2)
