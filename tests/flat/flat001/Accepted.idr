-- Signatures of flat functions that are accepted: every run-time argument
-- and the result are flat.
--
-- A flat function is one compiled in the flat regime: every value it handles
-- is held in registers, a machine word or a double each, and none needs the
-- heap. A directive `%cg native flat <name>` marks it; its signature decides
-- whether it can be flat, and the check reports it where the module is built
-- (flat002 has the signatures that are rejected). A type is flat when its
-- values fit in registers: a machine integer, `Char`, `Double`, and any data
-- type that is not recursive and whose run-time fields are flat. Erased
-- arguments and fields take no part.
--
-- The comments below say, for each function, the registers its arguments
-- take: as if it had been written with them as its arguments. Under any
-- other code generator than the native one and the flat oracle, the
-- functions run as ordinary Idris. The test runs `main`, which is ordinary
-- and calls them, twice: under Chez, and under the flat oracle, which
-- compiles each flat function from its flat form. The outputs agree.

record Point where
  constructor MkPoint
  x : Double
  y : Double

-- One constructor and no run-time fields: a token.
record Ordo where
  constructor MkOrdo

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

Peek Ordo where
  peek a m = m # (a + 1)

-- A record of two doubles takes two registers, as if written
-- `norm2 : Double -> Double -> Double` with `norm2 x y = x * x + y * y`.
%cg native flat Main.norm2
norm2 : Point -> Double
norm2 p = p.x * p.x + p.y * p.y

-- A pair takes its two fields' registers, a word each: a `Bool` is held as
-- its constructor's tag.
%cg native flat Main.swap
swap : Pair Bits64 Bool -> Pair Bool Bits64
swap (a, b) = (b, a)

-- An enumeration, and the narrow integers: a word each.
%cg native flat Main.pick
pick : Bool -> Bits8 -> Bits8 -> Bits8
pick c a b = if c then a else b

-- The index `k` is erased, so an `Addr k` is its one word, as if written
-- `offset : Bits64 -> Bits64 -> Bits64` with `offset w o = w + o`.
%cg native flat Main.offset
offset : Addr k -> Bits64 -> Addr k
offset (MkAddr w) o = MkAddr (w + o)

-- The erased `k` in `MkAnyAddr` takes no part either: one word, the
-- address's.
%cg native flat Main.kindless
kindless : AnyAddr -> Bits64
kindless (MkAnyAddr _ a) = a.word

-- Erased arguments take no part, as if written
-- `erasedNat : Bits64 -> Bits64` with `erasedNat w = w * 2`.
%cg native flat Main.erasedNat
erasedNat : (0 n : Nat) -> Bits64 -> Bits64
erasedNat _ w = w * 2

-- No constructors: no values, and no registers. It is never called.
%cg native flat Main.fromVoid
fromVoid : Void -> Bits64
fromVoid v impossible

-- Generic over an interface. The dictionary is static: it is known where
-- the function is called, not computed at run time. So this function has no
-- flat form of its own: each call from flat code gets a copy made for the
-- instance it uses, and the copy is judged. A copy at `Ordo`, the only
-- instance, would be as if written
--
--   twiceOrdo : Bits64 -> Op Ordo Bits64
--   twiceOrdo a m = let (m' # b) = peek a m in peek b m'   -- `peek` of `Peek Ordo`
--
-- whose `Ordo` is a token: one constructor and no fields, so no registers.
-- Here only the ordinary `main` calls it, so no copy is made.
%cg native flat Main.twice
twice : Peek h => Bits64 -> Op h Bits64
twice a m = let (m' # b) = peek a m in peek b m'

-- `IO ()` and `PrimIO` are functions of the world, which take it as one
-- more argument, as if written
--
--   nothing : PrimIO ()
--   nothing w = MkIORes () w
--
-- The world, `%World`, takes no register: it only orders the effects.
%cg native flat Main.nothing
nothing : IO ()
nothing = pure ()

%cg native flat Main.tick
tick : Bits64 -> PrimIO Bits64
tick n w = MkIORes (n + 1) w

-- Nested instances of one type constructor are not recursion: `Pair`'s
-- declaration mentions no type constructor. A triple is a pair in a pair,
-- three words, as if written `sum3 : Bits64 -> Bits64 -> Bits64 -> Bits64`.
%cg native flat Main.sum3
sum3 : (Bits64, Bits64, Bits64) -> Bits64
sum3 (a, b, c) = a + b + c

record Wrap a where
  constructor MkWrap
  inner : a

-- A record of one field takes the field's registers: one word.
%cg native flat Main.unwrap2
unwrap2 : Wrap (Wrap Bits64) -> Bits64
unwrap2 w = w.inner.inner

-- The token `m` takes no register; the result is the pair's two words.
%cg native flat Main.peekPair
peekPair : Bits64 -> Op Ordo (Bits64, Bool)
peekPair a m = m # (a, a == 0)

-- Sums that are not recursive. A value of a type of several constructors
-- takes a word for its constructor's tag, then each constructor's fields'
-- registers in turn, sharing none: `Maybe Bits64` takes a tag and `Just`'s
-- word, which is unused when the tag says `Nothing`.
%cg native flat Main.orZero
orZero : Maybe Bits64 -> Bits64
orZero Nothing = 0
orZero (Just x) = x

-- A tag, `Left`'s word and `Right`'s double: three registers.
%cg native flat Main.either
either : Either Bits64 Double -> Double
either (Left n) = cast n
either (Right d) = d

data Shape = Circle Point Double | Rect Point Point

-- A tag, `Circle`'s three doubles and `Rect`'s four: eight registers.
%cg native flat Main.width
width : Shape -> Double
width (Circle _ r) = 2 * r
width (Rect p q) = q.x - p.x

-- A tag, and `Just`'s field, a `Maybe Bits64` of a tag and a word: three
-- words.
%cg native flat Main.inner
inner : Maybe (Maybe Bits64) -> Bits64
inner (Just (Just x)) = x
inner _ = 0

-- A function argument whose own argument and result are flat: the function
-- has no form of its own, since a function is static, and each call gets a
-- copy at the function it passes.
%cg native flat Main.applyTwice
applyTwice : (Bits64 -> Bits64) -> Bits64 -> Bits64
applyTwice f x = f (f x)

-- Its two calls pass two functions, so `applyTwice` gets two copies, as if
-- written
--
--   applyTwicePlus : Bits64 -> Bits64 -> Bits64
--   applyTwicePlus x k = (x + k) + k
--
--   applyTwiceDouble : Bits64 -> Bits64
--   applyTwiceDouble x = (x * 2) * 2
--
-- and `useTwice k = applyTwicePlus 1 k + applyTwiceDouble k`. The section
-- `(+ k)` refers to `k`, a value known only at run time, so its copy takes
-- `k` as one more argument, after its own; `(* 2)` refers to nothing.
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
  let (MkOrdo # r) = twice 40 MkOrdo
  printLn r
  nothing
  t <- fromPrim (tick 41)
  printLn t
  printLn (sum3 (1, 2, 3))
  printLn (unwrap2 (MkWrap (MkWrap 5)))
  let (MkOrdo # pr) = peekPair 0 MkOrdo
  printLn pr
  printLn (orZero (Just 8), orZero Nothing)
  printLn (either (Left 2), either (Right 2.5))
  printLn (width (Circle (MkPoint 0 0) 1.5), width (Rect (MkPoint 1 0) (MkPoint 4 2)))
  printLn (inner (Just (Just 6)), inner (Just Nothing))
  printLn (useTwice 5)
