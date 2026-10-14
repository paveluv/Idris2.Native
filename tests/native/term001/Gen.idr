-- The term IR, written by hand through its builder: a program that runs,
-- using every construct the rendering supports, and a program with every
-- other construct, whose IR is printed.
--
-- The term IR is what the backend compiles both ordinary and flat code to:
-- a typed term, so that an ill-formed program does not compile (term002).
-- A function has one of two conventions. A CPS function is ordinary code:
-- its values are uniform, it returns to a continuation, and a call that is
-- not a tail call names the code after it as its continuation. A Direct
-- function is flat code: a machine function on words and doubles, which
-- returns its results. Each body below says the Idris it stands for.
--
-- A crash jumps to the runtime's `crash`, the entry calls the runtime's
-- `start`, and allocation's slow paths call its `allocSlow` and
-- `allocMutable`, which the program defines itself, as the runtime
-- library's flat forms would be, under the names the runtime contract gives
-- them.
module Main

import Compiler.Native.ELF
import Compiler.Native.HeapObject.BignumEnc
import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind
import Compiler.Native.HeapObject.StringEnc
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Area
import Compiler.Native.IRCommon.ConIds
import Compiler.Native.IRCommon.Operators.ArithOp
import Compiler.Native.IRCommon.Operators.ConvOp
import Compiler.Native.IRCommon.Operators.FOp
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.IRCommon.Operators.SubWord
import Compiler.Native.IRCommon.Operators.UnOp
import Compiler.Native.IRCommon.Ty
import Compiler.Native.Link
import Compiler.Native.Linkage.Routine
import Compiler.Native.LocatedIR.Dump
import Compiler.Native.LocatedIR.Program
import Compiler.Native.RegAlloc
import Compiler.Native.TermIR.Body
import Compiler.Native.TermIR.Build
import Compiler.Native.TermIR.Conv
import Compiler.Native.TermIR.Decls
import Compiler.Native.TermIR.Def
import Compiler.Native.TermIR.FieldTys
import Compiler.Native.TermIR.Instr
import Compiler.Native.TermIR.IsInt
import Compiler.Native.TermIR.Mem
import Compiler.Native.TermIR.Opnd
import Compiler.Native.TermIR.OvOp
import Compiler.Native.TermIR.Program
import Compiler.Native.TermIR.Sig
import Compiler.Native.TermIR.Sizes
import Compiler.Native.TermIR.StaticDef
import Compiler.Native.TermIR.StaticSig
import Compiler.Native.TermIR.Var
import Compiler.Native.X86.Encode
import Compiler.Native.X86.Render
import Compiler.Native.X86.Target
import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.Distinct
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.Vect
import System.File

%default total

TestEnc : Enc
TestEnc = defaultEnc

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

-- Immediates under the test's encoding: their proofs are searched where the
-- encoding is known.
val : (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd vr (Val {enc = TestEnc})
val i = Vx {enc = TestEnc} i {ok}

fix : (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd vr (Fix {enc = TestEnc})
fix i = Fx {enc = TestEnc} i {ok}

------------------------------------------------------------------------------
-- A program that runs: every construct the rendering supports

Run : Decls TestEnc
Run = MkDecls
  [ MkSig (nm "main") InCPS [] False
  , MkSig (nm "pair") InCPS [Val, Val] False
  , MkSig (nm "sumTo") (InDirect [W64] False) [W64] False
  , MkSig (nm "slowAdd") (InDirect [Val] False) [Val, Val] False
  , MkSig (nm "addTo") InCPS [Val, Val] False
  , MkSig (nm "same") InCPS [Val] False
  , MkSig (nm "divMod") (InDirect [W64, W64] False) [W64, W64] False
  , MkSig (nm "floats") (InDirect [W64] False) [F64, F64] False
  , MkSig (nm "bytes") (InDirect [W64] False) [] False
  , MkSig (flatName runtimeCrash) (InDirect [] False) [W64, W64] False
  , MkSig (flatName runtimeStart) (InDirect [] False) [W64, W64] False
  , MkSig (flatName runtimeAllocSlow) (InDirect [W64] False) [W64] False
  , MkSig (flatName runtimeAllocMutable) (InDirect [W64] False) [W64] False ]
  [ MkStaticSig (nm "two") CON ]

pairRef : Var (sigs Run) (MkSig (nm "pair") InCPS [Val, Val] False)
pairRef = later here

sumToRef : Var (sigs Run) (MkSig (nm "sumTo") (InDirect [W64] False) [W64] False)
sumToRef = later (later here)

slowAddRef : Var (sigs Run) (MkSig (nm "slowAdd") (InDirect [Val] False) [Val, Val] False)
slowAddRef = later (later (later here))

addToRef : Var (sigs Run) (MkSig (nm "addTo") InCPS [Val, Val] False)
addToRef = later (later (later (later here)))

sameRef : Var (sigs Run) (MkSig (nm "same") InCPS [Val] False)
sameRef = later (later (later (later (later here))))

divModRef : Var (sigs Run) (MkSig (nm "divMod") (InDirect [W64, W64] False) [W64, W64] False)
divModRef = later (later (later (later (later (later here)))))

floatsRef : Var (sigs Run) (MkSig (nm "floats") (InDirect [W64] False) [F64, F64] False)
floatsRef = later (later (later (later (later (later (later here))))))

bytesRef : Var (sigs Run) (MkSig (nm "bytes") (InDirect [W64] False) [] False)
bytesRef = later (later (later (later (later (later (later (later here)))))))

twoRef : Var (statics Run) (MkStaticSig (nm "two") CON)
twoRef = here

||| The runtime's `start`, reduced to what this program needs: the first
||| allocation window, mapped, of `window` bytes, as the allocation pointer
||| and its limit. The stack limit stays 0, so the stack is not checked.
startBody : Closed Run (InDirect [] False) False [W64, W64]
startBody = build $ \[entry, window] => do
  -- mmap(NULL, window, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
  w <- emit1 (SystemCall (W 9) [W 0, window, W 3, W 0x22, W (-1), W 0])
  emit0 (WriteHp w)
  lim <- emit1 (Arith Add w window)
  emit0 (WriteHpLim lim)
  ret []

||| The runtime's allocation slow path, reduced to what this program needs:
||| a fresh megabyte and `bytes` more from the system, the object at its
||| start, and the rest the allocation window. Nothing is collected.
allocSlowBody : Closed Run (InDirect [W64] False) False [W64]
allocSlowBody = build $ \[bytes] => do
  size <- emit1 (Arith Add bytes (W 1048576))
  -- mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
  w <- emit1 (SystemCall (W 9) [W 0, size, W 3, W 0x22, W (-1), W 0])
  hp <- emit1 (Arith Add w bytes)
  emit0 (WriteHp hp)
  lim <- emit1 (Arith Add w size)
  emit0 (WriteHpLim lim)
  ret [w]

||| The runtime's `allocMutable`, which allocates a mutable object by a
||| call: here the slow path's body, since nothing distinguishes the two.
allocMutableBody : Closed Run (InDirect [W64] False) False [W64]
allocMutableBody = build $ \[bytes] => do
  size <- emit1 (Arith Add bytes (W 1048576))
  w <- emit1 (SystemCall (W 9) [W 0, size, W 3, W 0x22, W (-1), W 0])
  hp <- emit1 (Arith Add w bytes)
  emit0 (WriteHp hp)
  lim <- emit1 (Arith Add w size)
  emit0 (WriteHpLim lim)
  ret [w]

||| The runtime's `crash`: the message, `length` bytes at `message`, written
||| to the standard error, then the process ended with status 1.
crashBody : Closed Run (InDirect [] False) False [W64, W64]
crashBody = build $ \[message, length] => do
  _ <- emit1 (SystemCall (W 1) [W 2, message, length, W 0, W 0, W 0])
  _ <- emit1 (SystemCall (W 231) [W 1, W 0, W 0, W 0, W 0, W 0])
  ret []

||| Unbounded addition of two `Val`s: the fixnum fast path, and `slowAdd` when
||| either is not a fixnum or the sum overflows, both slow cases in one block,
||| both paths meeting at a join. This is how ordinary code computes `x + y`
||| at `Integer`.
addInteger : Opnd vr Val -> Opnd vr Val -> Build Run c False vr l (Opnd vr Val)
addInteger x y = do
  [s] <- joinPoint [Val] $ \exit => do
    slow <- block [] $ \[] => do
      [r] <- directCall slowAddRef [x, y]
      exit [r]
    ifFixnums [x, y]
      (\[a, b] => arithOv OvAdd a b (\f => do w <- emit1 (WidenFix f); exit [w]) (slow []))
      (slow [])
  pure s

||| A case on a constructor, with a join: the sum of a pair's fields, as
||| `case p of MkPair a b => a + b` at `Integer`.
sumFields : Opnd vr Val -> Build Run c False vr l (Opnd vr Val)
sumFields p = do
  q <- emit1 (NarrowPtr CON p)
  tag <- emit1 (LoadPart ConId q)
  [r] <- joinPoint [Val] $ \exit =>
    switch tag
      [ (0, do a <- emit1 (Load Val (MkMem (AtPtr q) Nothing 8))
               b <- emit1 (Load Val (MkMem (AtPtr q) Nothing 16))
               s <- addInteger a b
               exit [s])
      , (7, unsupported "a constructor this test never makes") ]
      (crash "no such constructor")
  pure r

||| `pair a b = MkPair a b`: an object of constructor id 0 with two fields.
pairBody : Closed Run InCPS False [Val, Val]
pairBody = build $ \[a, b] => do
  p <- emit1 (AllocObj (ConH 0 2) [a, b])
  w <- emit1 (WidenPtr p)
  return w

||| 1 + 2 + … + n, by a loop, as the flat function
||| `sumTo : Bits64 -> Bits64` would be.
sumToBody : Closed Run (InDirect [W64] False) False [W64]
sumToBody = build $ \[n] =>
  loop [W64, W64] [n, W 0] $ \again, [i, acc] =>
    branch EqR i (W 0) (ret [acc]) $ do
      i' <- emit1 (Arith Sub i (W 1))
      acc' <- emit1 (Arith Add acc i)
      again [i', acc']

||| Stands in for the runtime's Integer addition: the test reaches it with a
||| fixnum and a pointer, and it doubles the fixnum, which tells the slow path
||| ran.
slowAddBody : Closed Run (InDirect [Val] False) False [Val, Val]
slowAddBody = build $ \[a, _] =>
  ifFixnums [a]
    (\[f] => arithOv OvAdd f f (\r => do w <- emit1 (WidenFix r); ret [w]) (crash "slowAdd: overflow"))
    (crash "slowAdd: not a fixnum")

||| A closure's code: the sum of its two arguments, through a tail call, as
||| `addTo a b = same (a + b)`.
addToBody : Closed Run InCPS False [Val, Val]
addToBody = build $ \[a, b] => do
  s <- addInteger a b
  tailCall sameRef [s]

||| `same x = x`.
sameBody : Closed Run InCPS False [Val]
sameBody = build $ \[x] => return x

||| Two results, as a flat function returning `(div a b, mod a b)` at
||| `Bits64` would.
divModBody : Closed Run (InDirect [W64, W64] False) False [W64, W64]
divModBody = build $ \[a, b] => do
  q <- emit1 (Arith DivS a b)
  r <- emit1 (Arith RemS a b)
  ret [q, r]

||| Whether a word is the one expected: 0 if so, 1 if not, so that the
||| failures of several checks add up.
failsUnless : Opnd vr W64 -> Int64 -> Build Run c False vr l (Opnd vr W64)
failsUnless x want = emit1 (Cmp NeR x (W want))

||| The sum of the words.
total' : List (Opnd vr W64) -> Build Run c False vr l (Opnd vr W64)
total' [] = pure (W 0)
total' (x :: xs) = do t <- total' xs; emit1 (Arith Add x t)

||| Double arithmetic, negation, constants and every comparison, a NaN's
||| among them, on 1.5 and 0.25: the number of checks that fail.
floatsBody : Closed Run (InDirect [W64] False) False [F64, F64]
floatsBody = build $ \[a, b] => do
  s <- emit1 (FArith FAdd a b)                         -- 1.75
  d <- emit1 (FArith FSub a b)                         -- 1.25
  four <- emit1 (FConst 4.0)
  half <- emit1 (FConst 0.5)
  p <- emit1 (FArith FMul d four)                      -- 5.0
  q <- emit1 (FArith FDiv p half)                      -- 10.0
  ten <- emit1 (FConst 10.0)
  sum <- emit1 (FConst 1.75)
  zero <- emit1 (FConst 0.0)
  nan <- emit1 (FArith FDiv zero zero)
  negZero <- emit1 (FNeg zero)
  negA <- emit1 (FNeg a)
  tenth <- emit1 (FConst 0.1)
  c1 <- emit1 (FCmp EqR s sum)
  c2 <- emit1 (FCmp EqR q ten)
  c3 <- emit1 (FCmp LtS a b)
  c4 <- emit1 (FCmp GtS a b)
  c5 <- emit1 (FCmp LeS b a)
  c6 <- emit1 (FCmp GeS a a)
  c7 <- emit1 (FCmp NeR a a)
  n1 <- emit1 (FCmp EqR nan nan)
  n2 <- emit1 (FCmp NeR nan nan)
  n3 <- emit1 (FCmp LtS nan a)
  n4 <- emit1 (FCmp LeS a nan)
  n5 <- emit1 (FCmp GtS nan a)
  n6 <- emit1 (FCmp GeS a nan)
  z1 <- emit1 (FCmp EqR negZero zero)
  zb <- emit1 (Convert FBits negZero)
  nb <- emit1 (Convert FBits negA)
  tb <- emit1 (Convert FBits tenth)
  m3 <- emit1 (Convert I2F (W (-3)))
  back <- emit1 (Convert F2I m3)
  fs <- traverse (uncurry failsUnless)
          [ (c1, 1), (c2, 1), (c3, 0), (c4, 1), (c5, 1), (c6, 1), (c7, 0)
          , (n1, 0), (n2, 1), (n3, 0), (n4, 0), (n5, 0), (n6, 0)
          , (z1, 1), (zb, -9223372036854775808), (nb, -4613937818241073152)
          , (tb, 4591870180066957722), (back, -3) ]
  t <- total' fs
  ret [t]

||| Narrow stores and loads, signed and not, into a string's bytes: the
||| number of checks that fail.
bytesBody : Closed Run (InDirect [W64] False) False []
bytesBody = build $ \[] => do
  str <- emit1 (AllocSized StringBytes (W 8) ())
  emit0 (StoreN Sub16 (MkMem (AtPtr str) (Just (W 0)) 8) (W 0x1FFFE))
  emit0 (StoreN Sub8 (MkMem (AtPtr str) (Just (W 3)) 8) (W 0x1FF))
  emit0 (StoreN Sub32 (MkMem (AtPtr str) (Just (W 1)) 8) (W 0x180000001))
  h1 <- emit1 (LoadN Sub16 True (MkMem (AtPtr str) Nothing 8))
  h2 <- emit1 (LoadN Sub16 False (MkMem (AtPtr str) Nothing 8))
  b1 <- emit1 (LoadN Sub8 True (MkMem (AtPtr str) (Just (W 3)) 8))
  b2 <- emit1 (LoadN Sub8 False (MkMem (AtPtr str) Nothing 11))
  w1 <- emit1 (LoadN Sub32 True (MkMem (AtPtr str) (Just (W 1)) 8))
  w2 <- emit1 (LoadN Sub32 False (MkMem (AtPtr str) Nothing 12))
  fs <- traverse (uncurry failsUnless)
          [(h1, -2), (h2, 65534), (b1, -1), (b2, 255), (w1, -2147483647), (w2, 2147483649)]
  t <- total' fs
  ret [t]

||| (20 + 9) + 7 + slowAdd 3 = 42 through calls, joins, a loop, the slow path,
||| a static, an array, two results, a closure and a round trip through
||| words and doubles, once the doubles' and the narrow accesses' checks
||| pass. The closure is as `addTo w`, `addTo` with one of its two arguments
||| filled, and applying it to `z` fills the second and calls `addTo`.
mainBody : Closed Run InCPS False []
mainBody = build $ \[] => do
  emit0 (Comment "a value live across a call")
  emit0 (Loc EmptyFC)
  seven <- emit1 (WidenFix (fix 7))
  p <- call pairRef [val 20, val 9]
  s <- sumFields p                              -- 29, the fast path
  t <- addInteger s seven                       -- 36
  [n] <- directCall sumToRef [W 2]              -- 3
  f <- emit1 (Tag n)
  three <- emit1 (WidenFix f)
  u <- addInteger three p                       -- p is a pointer: slowAdd, 6
  w <- addInteger t u                           -- 42
  two <- emit1 (StaticAddr twoRef)
  id <- emit1 (LoadPart ConId two)              -- 2
  arr <- emit1 (AllocSized ArrayElems (W 3) (val 0))
  idf <- emit1 (Tag id)
  idv <- emit1 (WidenFix idf)
  emit0 (Store Val (MkMem (AtPtr arr) (Just (W 1)) 8) idv)
  x <- emit1 (Load Val (MkMem (AtPtr arr) (Just (W 1)) 8))   -- 2
  [q, r] <- directCall divModRef [W 17, W 5]    -- 3, 2
  c <- emit1 (Cmp EqR r (W 2))
  branch NeR c (W 1) (crash "divMod: wrong remainder") $
   branch NeR q (W 3) (crash "divMod: wrong quotient") $ do
    oneHalf <- emit1 (FConst 1.5)
    quarter <- emit1 (FConst 0.25)
    [ff] <- directCall floatsRef [oneHalf, quarter]
    leaveIf NeR ff (W 0) (crash "floats: a check failed")
    [bf] <- directCall bytesRef []
    leaveIf NeR bf (W 0) (crash "bytes: a check failed")
    code <- emit1 (CodeAddr addToRef)
    clo <- emit1 (AllocObj (ClosureH 2 1) [code, w])
    cloV <- emit1 (WidenPtr clo)
    z <- addInteger x (val (-2))                -- 0
    res <- apply cloV z                         -- addTo 42 0
    rf <- emit1 (NarrowFix res)
    rw <- emit1 (Untag rf)
    neg <- emit1 (Unary Negate rw)
    pos <- emit1 (Unary Negate neg)
    dbl <- emit1 (Convert I2F pos)
    back <- emit1 (Convert F2I dbl)
    small <- emit1 (Ext Sub8 True back)
    out <- emit1 (Tag small)
    outV <- emit1 (WidenFix out)
    return outV

------------------------------------------------------------------------------
-- A program with every other construct, whose IR is dumped

Cover : Decls TestEnc
Cover = MkDecls
  [ MkSig (nm "cmain") InCPS [] False
  , MkSig (NS (mkNamespace "Main.Memory") (UN (Basic "roundTrip"))) (InDirect [W64] False) [W64] True
  , MkSig (UN (Basic "idris_routine")) (InDirect [] True) [] False ]
  []

roundTripRef : Var (sigs Cover) (MkSig (NS (mkNamespace "Main.Memory") (UN (Basic "roundTrip"))) (InDirect [W64] False) [W64] True)
roundTripRef = later here

routineRef : Var (sigs Cover) (MkSig (UN (Basic "idris_routine")) (InDirect [] True) [] False)
routineRef = later (later here)

||| The word/address conversions, in a function that may make them. Only the
||| runtime's own code may turn a word into an address, and the producer
||| decides which functions those are by their module, here `Main.Memory`.
roundTripBody : Closed Cover (InDirect [W64] False) True [W64]
roundTripBody = build $ \[w] => do
  p <- emit1 (WordToAddr CON w)
  w' <- emit1 (AddrToWord p)
  ret [w']

coverBody : Closed Cover InCPS False []
coverBody = build $ \[] => do
  one <- emit1 (FConst 1.5)
  two <- emit1 (FArith FAdd one one)
  neg <- emit1 (FNeg two)
  lt <- emit1 (FCmp LtS neg one)
  bits <- emit1 (Convert FBits two)
  dbl <- emit1 (Convert BitsF bits)
  scratch <- emit1 (AreaAddr SCRATCH)
  byte <- emit1 (LoadN Sub8 False (MkMem (AtWord scratch) Nothing 0))
  emit0 (StoreN Sub16 (MkMem (AtWord scratch) (Just (W 1)) 0) byte)
  hp <- emit1 ReadHp
  emit0 (WriteHp hp)
  lim <- emit1 ReadHpLim
  emit0 (WriteHpLim lim)
  k <- emit1 ReadK
  emit0 (WriteK k)
  sp <- emit1 ReadStackPointer
  emit0 (WriteStackPointer sp)
  pid <- emit1 (SystemCall (W 39) [])
  str <- emit1 (AllocSized StringBytes (W 5) ())
  hdr <- emit1 (LoadHeader str)
  i64 <- emit1 (AllocObj Int64H [W 5])
  d64 <- emit1 (AllocObj DoubleH [dbl])
  ref <- emit1 (AllocObj IORefH [Erased])
  ptr <- emit1 (AllocObj PtrH [hdr])
  arr <- emit1 (AllocObj (ArrayH 2) [val 1, val 2])
  bytes <- emit1 (AllocObj (StringH True 3) [W 0])
  buf <- emit1 (AllocObj (BufferH 9) [W 0, W 0])
  [w] <- directCall roundTripRef [lt]
  _ <- directCall routineRef []
  i64v <- emit1 (WidenPtr i64)
  tagOv w (\f => do v <- emit1 (WidenFix f); enter pid [v, i64v]) (tailApply i64v i64v)

------------------------------------------------------------------------------
-- Through the pipeline

covering
main : IO ()
main = do
  let Just m = close mainBody | Nothing => putStrLn "main: a level outside its context"
  let Just p = close pairBody | Nothing => putStrLn "pair: a level outside its context"
  let Just s = close sumToBody | Nothing => putStrLn "sumTo: a level outside its context"
  let Just sa = close slowAddBody | Nothing => putStrLn "slowAdd: a level outside its context"
  let Just at = close addToBody | Nothing => putStrLn "addTo: a level outside its context"
  let Just sm = close sameBody | Nothing => putStrLn "same: a level outside its context"
  let Just dm = close divModBody | Nothing => putStrLn "divMod: a level outside its context"
  let Just fl = close floatsBody | Nothing => putStrLn "floats: a level outside its context"
  let Just by = close bytesBody | Nothing => putStrLn "bytes: a level outside its context"
  let Just cr = close crashBody | Nothing => putStrLn "crash: a level outside its context"
  let Just st = close startBody | Nothing => putStrLn "start: a level outside its context"
  let Just al = close allocSlowBody | Nothing => putStrLn "allocSlow: a level outside its context"
  let Just am = close allocMutableBody | Nothing => putStrLn "allocMutable: a level outside its context"
  -- the names' distinctness decided here, as a producer decides it
  let Left ok = choose (distinct (map (.name) (sigs Run)) && distinct (map (.sym) (statics Run)))
    | Right _ => putStrLn "the running program: names repeat"
  let run = allocRegs x86_64 (MkProgram {d = Run} [Defined m, Defined p, Defined s, Defined sa, Defined at, Defined sm, Defined dm, Defined fl, Defined by, Defined cr, Defined st, Defined al, Defined am]
                                   [MkStaticDef (ConH 2 0) []] (MkEntry here) noConIds)
  let Right rendered = render TestEnc run
    | Left err => putStrLn ("render: " ++ err)
  let Right image = linkProgram TestEnc windowBytes rendered.areas rendered.text rendered.rodata
    | Left problems => putStrLn ("link: " ++ show problems)
  Right () <- writeImage "term" image
    | Left err => putStrLn ("write: " ++ show err)
  let Just c = close coverBody | Nothing => putStrLn "cmain: a level outside its context"
  let Just rt = close roundTripBody | Nothing => putStrLn "roundTrip: a level outside its context"
  -- the names' distinctness decided here, as a producer decides it
  case choose (distinct (map (.name) (sigs Cover)) && distinct (map (.sym) (statics Cover))) of
    Left ok => do
      let cover = allocRegs x86_64 (MkProgram {d = Cover} [Defined c, Defined rt, External] [] (MkEntry here) noConIds)
      putStr (dumpProgram cover)
    Right _ => putStrLn "the covering program: names repeat"
