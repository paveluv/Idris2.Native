-- Signatures of flat functions that are accepted: every run-time argument
-- and the result are flat. Under any other code generator than the native
-- one and the flat oracle, the functions run as ordinary Idris.

record Point where
  constructor MkPoint
  x : Double
  y : Double

-- One constructor and no run-time fields: a token.
record Heap where
  constructor MkHeap

data Ret : Type -> Type -> Type where
  (#) : (1 m : h) -> (v : a) -> Ret h a

Op : Type -> Type -> Type
Op h a = (1 m : h) -> Ret h a

data Kind = CON | CLOSURE

-- An index the field does not need.
record Addr (0 k : Kind) where
  constructor MkAddr
  word : Bits64

-- An erased index that the type does not determine.
data AnyAddr : Type where
  MkAnyAddr : (0 k : Kind) -> Addr k -> AnyAddr

interface Peek (0 h : Type) where
  peek : Bits64 -> Op h Bits64

Peek Heap where
  peek a m = m # (a + 1)

%cg native flat Main.norm2
norm2 : Point -> Double
norm2 p = p.x * p.x + p.y * p.y

%cg native flat Main.swap
swap : Pair Bits64 Bool -> Pair Bool Bits64
swap (a, b) = (b, a)

-- An enumeration, and the narrow integers.
%cg native flat Main.pick
pick : Bool -> Bits8 -> Bits8 -> Bits8
pick c a b = if c then a else b

%cg native flat Main.offset
offset : Addr k -> Bits64 -> Addr k
offset (MkAddr w) o = MkAddr (w + o)

%cg native flat Main.kindless
kindless : AnyAddr -> Bits64
kindless (MkAnyAddr _ a) = a.word

-- Erased arguments take no part.
%cg native flat Main.erasedNat
erasedNat : (0 n : Nat) -> Bits64 -> Bits64
erasedNat _ w = w * 2

-- No constructors: no values.
%cg native flat Main.fromVoid
fromVoid : Void -> Bits64
fromVoid v impossible

-- Generic over an interface: the dictionary and the token are judged in the
-- function's specialisations.
%cg native flat Main.twice
twice : Peek h => Bits64 -> Op h Bits64
twice a m = let (m' # b) = peek a m in peek b m'

-- `IO ()` and `PrimIO` are functions of the world.
%cg native flat Main.nothing
nothing : IO ()
nothing = pure ()

%cg native flat Main.tick
tick : Bits64 -> PrimIO Bits64
tick n w = MkIORes (n + 1) w

-- Nested instances of one type constructor are not recursion: `Pair`'s
-- declaration mentions no type constructor.
%cg native flat Main.sum3
sum3 : (Bits64, Bits64, Bits64) -> Bits64
sum3 (a, b, c) = a + b + c

record Wrap a where
  constructor MkWrap
  inner : a

%cg native flat Main.unwrap2
unwrap2 : Wrap (Wrap Bits64) -> Bits64
unwrap2 w = w.inner.inner

%cg native flat Main.peekPair
peekPair : Bits64 -> Op Heap (Bits64, Bool)
peekPair a m = m # (a, a == 0)

-- Sums that are not recursive.
%cg native flat Main.orZero
orZero : Maybe Bits64 -> Bits64
orZero Nothing = 0
orZero (Just x) = x

%cg native flat Main.either
either : Either Bits64 Double -> Double
either (Left n) = cast n
either (Right d) = d

data Shape = Circle Point Double | Rect Point Point

%cg native flat Main.width
width : Shape -> Double
width (Circle _ r) = 2 * r
width (Rect p q) = q.x - p.x

%cg native flat Main.inner
inner : Maybe (Maybe Bits64) -> Bits64
inner (Just (Just x)) = x
inner _ = 0

-- A function argument whose own argument and result are flat: the function
-- has no form of its own, and each call gets a copy at the function it
-- passes.
%cg native flat Main.applyTwice
applyTwice : (Bits64 -> Bits64) -> Bits64 -> Bits64
applyTwice f x = f (f x)

%cg native flat Main.useTwice
useTwice : Bits64 -> Bits64
useTwice k = applyTwice (+ k) 1 + applyTwice (* 2) k

main : IO ()
main = do
  printLn (norm2 (MkPoint 3 4))
  printLn (swap (7, True))
  printLn (pick False 1 2)
  printLn (offset (MkAddr {k = CON} 40) 2).word
  printLn (kindless (MkAnyAddr CLOSURE (MkAddr 9)))
  printLn (erasedNat 3 21)
  let (MkHeap # r) = twice 40 MkHeap
  printLn r
  nothing
  t <- fromPrim (tick 41)
  printLn t
  printLn (sum3 (1, 2, 3))
  printLn (unwrap2 (MkWrap (MkWrap 5)))
  let (MkHeap # pr) = peekPair 0 MkHeap
  printLn pr
  printLn (orZero (Just 8), orZero Nothing)
  printLn (either (Left 2), either (Right 2.5))
  printLn (width (Circle (MkPoint 0 0) 1.5), width (Rect (MkPoint 1 0) (MkPoint 4 2)))
  printLn (inner (Just (Just 6)), inner (Just Nothing))
  printLn (useTwice 5)
