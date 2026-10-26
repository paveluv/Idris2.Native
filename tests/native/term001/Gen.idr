-- The term IR, written by hand through its builder: a program that runs,
-- using every construct the rendering supports, built under two value
-- encodings, fixnum tag 1 and fixnum tag 0, and run under each; and a
-- program with every other construct, whose IR is printed.
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

import Core.FC
import Core.Name
import Core.Name.Namespace
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Native.Area
import Native.Codegen.ELF
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Link
import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.LocatedIR.Dump
import Native.Codegen.LocatedIR.Program
import Native.Codegen.RegAlloc
import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Build
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Def
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Mem
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.OvOp
import Native.Codegen.TermIR.Program
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.Sizes
import Native.Codegen.TermIR.StaticDef
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var
import Native.Codegen.X86.Encode
import Native.Codegen.X86.Render
import Native.Codegen.X86.Target
import Native.Data.Builder
import Native.Data.Distinct
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.Port
import Native.Primitive
import Native.Routine
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.IntegerRoutine
import Native.Types.Kind
import Native.Types.StringEnc
import Native.Types.StringRoutine
import Native.Width
import System.File

%default total

||| The default encodings, with fixnum tag 1: a fixnum n is the word 2n + 1,
||| a pointer the object's address.
TestEnc : Enc
TestEnc = defaultEnc

||| The encodings with fixnum tag 0: a fixnum n is the word 2n, a pointer
||| the object's address plus 1.
Tag0Enc : Enc
Tag0Enc = { val := FixnumTag0 } defaultEnc

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

------------------------------------------------------------------------------
-- A program that runs: every construct the rendering supports

-- The runtime's routines as a loaded runtime's record would give them
-- (`Native.Runtime.Routines.routines`): this program writes the routines'
-- bodies itself, under the names the runtime's functions have, and hands
-- the code generator the record of them, as `realise` does from the TTCs.
-- The rendering puts each routine's symbol at its function by this record.
runtimeStart, runtimeAllocSlow, runtimeAllocMutable, runtimeCrash : Name
runtimeStart = NS (runtimeModule "Start") (UN (Basic "start"))
runtimeAllocSlow = NS (runtimeModule "Space") (UN (Basic "allocSlow"))
runtimeAllocMutable = NS (runtimeModule "Space") (UN (Basic "allocMutable"))
runtimeCrash = NS (runtimeModule "System") (UN (Basic "crash"))

realised : Realised
realised =
  MkRealised [(runtimeStart, Start),
              (runtimeAllocSlow, AllocSlow), (runtimeAllocMutable, AllocMutable),
              (runtimeCrash, Crash)]
             Nothing Nothing empty empty empty empty empty

-- The program, under any value encoding with fixnums: `writeRun` builds it
-- once for each.
parameters {enc : Enc} {auto 0 fx : HasFixnums enc.val}
  -- Immediates: their proofs are searched where the integer is known.
  val : (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd vr (Val {enc})
  val i = Vx {enc} i {ok}

  fix : (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd vr (Fix {enc})
  fix i = Fx {enc} i {ok}

  Run : Decls enc
  Run = MkDecls
    [ MkSig (nm "main") CPS [] False
    , MkSig (nm "pair") CPS [Val, Val] False
    , MkSig (nm "sumTo") (Direct [W64] False) [W64] False
    , MkSig (nm "slowAdd") (Direct [Val] False) [Val, Val] False
    , MkSig (nm "addTo") CPS [Val, Val] False
    , MkSig (nm "same") CPS [Val] False
    , MkSig (nm "divMod") (Direct [W64, W64] False) [W64, W64] False
    , MkSig (nm "floats") (Direct [W64] False) [F64, F64] False
    , MkSig (nm "bytes") (Direct [W64] False) [] False
    , MkSig (nm "fromStatics") CPS [] False
    , MkSig (flatName runtimeCrash) (Direct [] False) [W64, W64] False
    , MkSig (flatName runtimeStart) (Direct [] False) [W64, W64] False
    , MkSig (flatName runtimeAllocSlow) (Direct [W64] False) [W64] False
    , MkSig (flatName runtimeAllocMutable) (Direct [W64] False) [W64] False ]
    [ MkStaticSig (nm "two") CON
    , MkStaticSig (nm "cell") CON
    , MkStaticSig (nm "big") INT64
    , MkStaticSig (nm "plus30") CLOSURE ]

  pairRef : Var (sigs Run) (MkSig (nm "pair") CPS [Val, Val] False)
  pairRef = later here

  sumToRef : Var (sigs Run) (MkSig (nm "sumTo") (Direct [W64] False) [W64] False)
  sumToRef = later (later here)

  slowAddRef : Var (sigs Run) (MkSig (nm "slowAdd") (Direct [Val] False) [Val, Val] False)
  slowAddRef = later (later (later here))

  addToRef : Var (sigs Run) (MkSig (nm "addTo") CPS [Val, Val] False)
  addToRef = later (later (later (later here)))

  sameRef : Var (sigs Run) (MkSig (nm "same") CPS [Val] False)
  sameRef = later (later (later (later (later here))))

  divModRef : Var (sigs Run) (MkSig (nm "divMod") (Direct [W64, W64] False) [W64, W64] False)
  divModRef = later (later (later (later (later (later here)))))

  floatsRef : Var (sigs Run) (MkSig (nm "floats") (Direct [W64] False) [F64, F64] False)
  floatsRef = later (later (later (later (later (later (later here))))))

  bytesRef : Var (sigs Run) (MkSig (nm "bytes") (Direct [W64] False) [] False)
  bytesRef = later (later (later (later (later (later (later (later here)))))))

  fromStaticsRef : Var (sigs Run) (MkSig (nm "fromStatics") CPS [] False)
  fromStaticsRef = later (later (later (later (later (later (later (later (later here))))))))

  twoRef : Var (statics Run) (MkStaticSig (nm "two") CON)
  twoRef = here

  cellRef : Var (statics Run) (MkStaticSig (nm "cell") CON)
  cellRef = later here

  bigRef : Var (statics Run) (MkStaticSig (nm "big") INT64)
  bigRef = later (later here)

  plus30Ref : Var (statics Run) (MkStaticSig (nm "plus30") CLOSURE)
  plus30Ref = later (later (later here))

  ||| The runtime's `start`, reduced to what this program needs: the first
  ||| allocation window, mapped, of `window` bytes, as the allocation pointer
  ||| and its limit. The stack limit stays 0, so the stack is not checked.
  startBody : Closed Run (Direct [] False) False [W64, W64]
  startBody = build $ \[entry, window] => do
    -- mmap(NULL, window, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
    w <- emit1 (SystemCall 6 [W 9, W 0, window, W 3, W 0x22, W (-1), W 0])
    -- the system gives the mapping's address as a word; the window's
    -- registers hold byte addresses, which the word is by a retyping, and
    -- which a count of bytes moves
    base <- emit1 (WordToByteAddr w)
    emit0 (SetPinned Hp base)
    lim <- emit1 (Offset base window)
    emit0 (SetPinned HpLim lim)
    ret []

  ||| The runtime's allocation slow path, reduced to what this program needs:
  ||| a fresh megabyte and `bytes` more from the system, the object at its
  ||| start, and the rest the allocation window. Nothing is collected.
  allocSlowBody : Closed Run (Direct [W64] False) False [W64]
  allocSlowBody = build $ \[bytes] => do
    size <- emit1 (Arith Add bytes (W 1048576))
    -- mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)
    w <- emit1 (SystemCall 6 [W 9, W 0, size, W 3, W 0x22, W (-1), W 0])
    base <- emit1 (WordToByteAddr w)
    hp <- emit1 (Offset base bytes)
    emit0 (SetPinned Hp hp)
    lim <- emit1 (Offset base size)
    emit0 (SetPinned HpLim lim)
    ret [w]

  ||| The runtime's `allocMutable`, which allocates a mutable object by a
  ||| call: here the slow path's body, since nothing distinguishes the two.
  allocMutableBody : Closed Run (Direct [W64] False) False [W64]
  allocMutableBody = build $ \[bytes] => do
    size <- emit1 (Arith Add bytes (W 1048576))
    w <- emit1 (SystemCall 6 [W 9, W 0, size, W 3, W 0x22, W (-1), W 0])
    base <- emit1 (WordToByteAddr w)
    hp <- emit1 (Offset base bytes)
    emit0 (SetPinned Hp hp)
    lim <- emit1 (Offset base size)
    emit0 (SetPinned HpLim lim)
    ret [w]

  ||| The runtime's `crash`: the message, `length` bytes at `message`, written
  ||| to the standard error, then the process ended with status 1.
  crashBody : Closed Run (Direct [] False) False [W64, W64]
  crashBody = build $ \[message, length] => do
    _ <- emit1 (SystemCall 6 [W 1, W 2, message, length, W 0, W 0, W 0])
    _ <- emit1 (SystemCall 6 [W 231, W 1, W 0, W 0, W 0, W 0, W 0])
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
    tag <- emit1 (LoadPart ConIdP q)
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
  pairBody : Closed Run CPS False [Val, Val]
  pairBody = build $ \[a, b] => do
    p <- emit1 (AllocObj (ConH 0 2) [a, b])
    w <- emit1 (WidenPtr p)
    return w

  ||| 1 + 2 + … + n, by a loop, as the flat function
  ||| `sumTo : Bits64 -> Bits64` would be.
  sumToBody : Closed Run (Direct [W64] False) False [W64]
  sumToBody = build $ \[n] =>
    loop [W64, W64] [n, W 0] $ \again, [i, acc] =>
      branch EqR i (W 0) (ret [acc]) $ do
        i' <- emit1 (Arith Sub i (W 1))
        acc' <- emit1 (Arith Add acc i)
        again [i', acc']

  ||| Stands in for the runtime's Integer addition: the test reaches it with a
  ||| fixnum and a pointer, and it doubles the fixnum, which tells the slow path
  ||| ran.
  slowAddBody : Closed Run (Direct [Val] False) False [Val, Val]
  slowAddBody = build $ \[a, _] =>
    ifFixnums [a]
      (\[f] =>
        arithOv OvAdd f f (\r => do w <- emit1 (WidenFix r); ret [w]) (crash "slowAdd: overflow"))
      (crash "slowAdd: not a fixnum")

  ||| A closure's code: the sum of its two arguments, through a tail call, as
  ||| `addTo a b = same (a + b)`.
  addToBody : Closed Run CPS False [Val, Val]
  addToBody = build $ \[a, b] => do
    s <- addInteger a b
    tailCall sameRef [s]

  ||| `same x = x`.
  sameBody : Closed Run CPS False [Val]
  sameBody = build $ \[x] => return x

  ||| Two results, as a flat function returning `(div a b, mod a b)` at
  ||| `Bits64` would.
  divModBody : Closed Run (Direct [W64, W64] False) False [W64, W64]
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
  floatsBody : Closed Run (Direct [W64] False) False [F64, F64]
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
  bytesBody : Closed Run (Direct [W64] False) False []
  bytesBody = build $ \[] => do
    str <- emit1 (AllocSized StringBytesP (W 8) ())
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

  -- Statics with fields, which the program never allocates: objects laid out
  -- in the image's read-only data, as a constant's value is, read by code
  -- through their addresses. As the Idris
  --
  --   data Cell = MkCell Int Integer Type
  --
  --   cell : Cell
  --   cell = MkCell big 7 Int         -- a type, as a value, is erased
  --
  --   big : Int
  --   big = 4611686018427387909       -- 2^62 + 5, outside the fixnum range
  --
  --   plus30 : Integer -> Integer
  --   plus30 = addTo 30               -- a partial application
  --
  -- `cell` is constructor 3 of three fields: `big`'s address, a static
  -- after it, as a pointer word; the fixnum 7; and the erased value. `big`
  -- is a box, as an `Int` outside the fixnum range is (`INT64`). `plus30`
  -- is a closure of `addTo`, whose arity is 2, with one argument filled:
  -- its words are `addTo`'s code address and the fixnum 30. The addresses
  -- are words of the data that the link writes once the image is laid out;
  -- the fixnums and the erased value are written as the value encoding
  -- has them.

  ||| Reads the statics as code reads any object, and checks each word:
  ||| `cell`'s constructor; its first field, a pointer, not a fixnum, to
  ||| `big`'s word; its other two fixnums, the last 0, the erased value;
  ||| `plus30`'s code word, the word a closure of `addTo` made at run time
  ||| holds. Then applies `plus30` to 7 + 5, as any closure is applied. As
  ||| `case cell of MkCell b s _ => if b == big then plus30 (s + 5) else …`,
  ||| which is 42.
  fromStaticsBody : Closed Run CPS False []
  fromStaticsBody = build $ \[] => do
    cell <- emit1 (StaticAddr cellRef)
    con <- emit1 (LoadPart ConIdP cell)
    leaveIf NeR con (W 3) (crash "cell: not constructor 3")
    b <- emit1 (Load Val (MkMem (AtPtr cell) Nothing 8))
    s <- emit1 (Load Val (MkMem (AtPtr cell) Nothing 16))
    e <- emit1 (Load Val (MkMem (AtPtr cell) Nothing 24))
    ifFixnums [b] (\_ => crash "cell: its first field is a fixnum") $ do
      bp <- emit1 (NarrowPtr INT64 b)
      bw <- emit1 (Load W64 (MkMem (AtPtr bp) Nothing 8))
      leaveIf NeR bw (W 4611686018427387909) (crash "cell: its first field is not big")
      ifFixnums [s, e]
        (\[sf, ef] => do
          ew <- emit1 (Untag ef)
          leaveIf NeR ew (W 0) (crash "cell: its last field is not the erased value")
          sw <- emit1 (Untag sf)
          twelve <- emit1 (Arith Add sw (W 5))
          tf <- emit1 (Tag twelve)
          tv <- emit1 (WidenFix tf)
          plus <- emit1 (StaticAddr plus30Ref)
          -- `addTo 30` made at run time, whose code word is `addTo`'s
          -- entry; the two code words compared, since entering `addTo` a
          -- byte or a few in can still give 42. A closure's word at an
          -- index is of no type its kind says, so each loads as a word.
          code <- emit1 (CodeOf addToRef)
          made <- emit1 (AllocObj (ClosureH 2 1) [code, val 30])
          pw <- emit1 (Load W64 (MkMem (AtPtr plus) (Just (W 0)) 8))
          mw <- emit1 (Load W64 (MkMem (AtPtr made) (Just (W 0)) 8))
          leaveIf NeR pw mw (crash "plus30: its code word is not addTo's")
          pv <- emit1 (WidenPtr plus)
          tailApply pv tv)
        (crash "cell: its second or third field is not a fixnum")

  ||| (20 + 9) + 7 + slowAdd 3 = 42 through calls, joins, a loop, the slow path,
  ||| a static, an array, two results, a closure and a round trip through
  ||| words and doubles, once the doubles' and the narrow accesses' checks
  ||| pass, and the statics give 42 too. The closure is as `addTo w`, `addTo`
  ||| with one of its two arguments filled, and applying it to `z` fills the
  ||| second and calls `addTo`.
  mainBody : Closed Run CPS False []
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
    id <- emit1 (LoadPart ConIdP two)              -- 2
    arr <- emit1 (AllocSized ArrayElemsP (W 3) (val 0))
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
      code <- emit1 (CodeOf addToRef)
      clo <- emit1 (AllocObj (ClosureH 2 1) [code, w])
      cloV <- emit1 (WidenPtr clo)
      z <- addInteger x (val (-2))                -- 0
      res <- apply cloV z                         -- addTo 42 0
      st <- call fromStaticsRef []                -- 42, from the statics
      rf <- emit1 (NarrowFix res)
      sf <- emit1 (NarrowFix st)
      leaveIf NeR sf rf (crash "fromStatics: not 42")
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
  [ MkSig (nm "cmain") CPS [] False
  , MkSig (NS (mkNamespace "Main.Memory") (UN (Basic "roundTrip"))) (Direct [W64] False) [W64] True
  , MkSig (UN (Basic "idris_routine")) (Direct [] True) [] False ]
  []

roundTripRef : Var (sigs Cover)
               (MkSig (NS (mkNamespace "Main.Memory") (UN (Basic "roundTrip"))) (Direct [W64] False)
                [W64] True)
roundTripRef = later here

routineRef : Var (sigs Cover) (MkSig (UN (Basic "idris_routine")) (Direct [] True) [] False)
routineRef = later (later here)

coverRef : Var (sigs Cover) (MkSig (nm "cmain") CPS [] False)
coverRef = here

||| The word/address conversions, in a function that may make them. Only the
||| runtime's own code may turn a word into an address, and the producer
||| decides which functions those are by their module, here `Main.Memory`.
roundTripBody : Closed Cover (Direct [W64] False) True [W64]
roundTripBody = build $ \[w] => do
  p <- emit1 (WordToAddr CON w)
  w' <- emit1 (AddrToWord p)
  ret [w']

coverBody : Closed Cover CPS False []
coverBody = build $ \[] => do
  one <- emit1 (FConst 1.5)
  two <- emit1 (FArith FAdd one one)
  neg <- emit1 (FNeg two)
  lt <- emit1 (FCmp LtS neg one)
  bits <- emit1 (Convert FBits two)
  dbl <- emit1 (Convert BitsF bits)
  scratch <- emit1 (AreaAddr SCRATCH)
  byte <- emit1 (LoadN Sub8 False (MkMem (AtBytes scratch) Nothing 0))
  emit0 (StoreN Sub16 (MkMem (AtBytes scratch) (Just (W 1)) 0) byte)
  -- A byte address moves by a count of bytes; it is a word only by a
  -- retyping, which takes no slot of its own and has no code: the dump
  -- shows the add, and the store at the same slot as the address.
  next <- emit1 (Offset scratch (W 8))
  word <- emit1 (ByteAddrToWord next)
  again <- emit1 (WordToByteAddr word)
  emit0 (StoreN Sub8 (MkMem (AtBytes again) Nothing 0) byte)
  hp <- emit1 (GetPinned Hp)
  emit0 (SetPinned Hp hp)
  lim <- emit1 (GetPinned HpLim)
  emit0 (SetPinned HpLim lim)
  k <- emit1 (GetPinned K)
  emit0 (SetPinned K k)
  pid <- emit1 (SystemCall 0 [W 39])
  str <- emit1 (AllocSized StringBytesP (W 5) ())
  hdr <- emit1 (LoadHeader str)
  i64 <- emit1 (AllocObj Int64H [W 5])
  d64 <- emit1 (AllocObj DoubleH [dbl])
  ref <- emit1 (AllocObj IORefH [Erased])
  ptr <- emit1 (AllocObj PtrH [hdr])
  arr <- emit1 (AllocObj (ArrayH 2) [val 1, val 2])
  bytes <- emit1 (AllocObj (StringH (MkUtf8Parts True 3)) [W 0])
  buf <- emit1 (AllocObj (BytesH 9) [W 0, W 0])
  [w] <- directCall roundTripRef [lt]
  _ <- directCall routineRef []
  i64v <- emit1 (WidenPtr i64)
  -- `Enter` jumps to a code address, never to a word
  code <- emit1 (CodeOf coverRef)
  tagOv w (\f => do v <- emit1 (WidenFix f); enter code [v, i64v]) (tailApply i64v i64v)


------------------------------------------------------------------------------
-- Through the pipeline

parameters {enc : Enc} {auto 0 fx : HasFixnums enc.val}
  ||| The running program under the encoding, rendered and linked into the
  ||| executable `file`.
  covering
  writeRun : String -> IO ()
  writeRun file = do
    let Just m = close (mainBody {enc}) | Nothing => putStrLn "main: a level outside its context"
    let Just p = close (pairBody {enc}) | Nothing => putStrLn "pair: a level outside its context"
    let Just s = close (sumToBody {enc}) | Nothing => putStrLn "sumTo: a level outside its context"
    let Just sa = close (slowAddBody {enc})
      | Nothing => putStrLn "slowAdd: a level outside its context"
    let Just at = close (addToBody {enc}) | Nothing => putStrLn "addTo: a level outside its context"
    let Just sm = close (sameBody {enc}) | Nothing => putStrLn "same: a level outside its context"
    let Just dm = close (divModBody {enc})
      | Nothing => putStrLn "divMod: a level outside its context"
    let Just fl = close (floatsBody {enc})
      | Nothing => putStrLn "floats: a level outside its context"
    let Just by = close (bytesBody {enc}) | Nothing => putStrLn "bytes: a level outside its context"
    let Just fs = close (fromStaticsBody {enc})
      | Nothing => putStrLn "fromStatics: a level outside its context"
    let Just cr = close (crashBody {enc}) | Nothing => putStrLn "crash: a level outside its context"
    let Just st = close (startBody {enc}) | Nothing => putStrLn "start: a level outside its context"
    let Just al = close (allocSlowBody {enc})
      | Nothing => putStrLn "allocSlow: a level outside its context"
    let Just am = close (allocMutableBody {enc})
      | Nothing => putStrLn "allocMutable: a level outside its context"
    -- the names' distinctness decided here, as a producer decides it
    let Left ok = choose (distinct (map (.name) (sigs (Run {enc})))
                          && distinct (map (.sym) (statics (Run {enc}))))
      | Right _ => putStrLn "the running program: names repeat"
    let run =
          allocRegs x86_64
            (MkProgram {d = Run {enc}}
              [Defined m, Defined p, Defined s, Defined sa, Defined at, Defined sm, Defined dm,
               Defined fl, Defined by, Defined fs, Defined cr, Defined st, Defined al, Defined am]
              [ MkStaticDef (ConH 2 0) []
              , MkStaticDef (ConH 3 3) [SRef (bigRef {enc}), SVal 7, SVal 0]
              , MkStaticDef Int64H [SWord 4611686018427387909]
              , MkStaticDef (ClosureH 2 1) [SCode (addToRef {enc}), SVal 30] ]
              (MkEntry here) noConIds)
    let Right rendered = render enc realised [] run
      | Left err => putStrLn ("render: " ++ err)
    let Right image = linkProgram enc windowBytes rendered.areas rendered.text rendered.rodata
      | Left problems => putStrLn ("link: " ++ show problems)
    Right () <- writeImage file image
      | Left err => putStrLn ("write: " ++ show err)
    pure ()

covering
main : IO ()
main = do
  writeRun {enc = TestEnc} "term"
  writeRun {enc = Tag0Enc} "term0"
  let Just c = close coverBody | Nothing => putStrLn "cmain: a level outside its context"
  let Just rt = close roundTripBody | Nothing => putStrLn "roundTrip: a level outside its context"
  -- the names' distinctness decided here, as a producer decides it
  case choose (distinct (map (.name) (sigs Cover)) && distinct (map (.sym) (statics Cover))) of
    Left ok => do
      let cover =
            allocRegs x86_64
              (MkProgram {d = Cover} [Defined c, Defined rt, External] [] (MkEntry here) noConIds)
      putStr (fastConcat (toList (dumpProgram cover)))
    Right _ => putStrLn "the covering program: names repeat"
