-- The value check (`Native.Codegen.ValueCheck`) as the oracle of register
-- allocation: every program the allocator is given, it must allocate so
-- that each location read holds the value the term reads there. Here the
-- programs are generated, a few hundred of them, each from a seed, and each
-- must be accepted.
--
-- A program has three functions, as the Idris
--
--     main : a
--     f : a -> a
--     g : a -> a -> a
--
-- each body made by the generator below from its seed: straight-line code
-- over the words and values it has made so far, which picks, step by
-- step, one of
--
--     w = x `op` y              -- any of the thirteen arithmetic ops,
--                               -- some of which want fixed registers
--     b = box w                 -- an allocation, which may collect
--     p = (u, v)                -- another, of two values
--     r = f u ; r = g u v       -- a call that is not a tail call
--     if x `rel` y then ...     -- an early exit, by any of the ten
--                               -- relations, half the rest each way
--     loop i acc                -- a loop, counting i down, its exit at 0
--                               -- the rest of the code
--     w = if x < y then x else x + 5   -- a join of two words
--
-- and, when its fuel runs out, ends with `return u`, `f u` or `g u v` in
-- tail position. Until it has made a word it reads the immediate 1; its
-- values start from the function's parameters (`main`'s from the
-- immediate 7). What it makes is counted from the term, so that a
-- generator gone degenerate shows in the counts.
module Main

import Core.Name
import Core.Name.Namespace
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Data.SortedSet
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty
import Native.Codegen.LocalAssign
import Native.Codegen.LocatedIR.Program
import Native.Codegen.RegAlloc
import Native.Codegen.RegMask
import Native.Codegen.Target
import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Build
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Def
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.Program
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.StaticDef
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var
import Native.Codegen.ValueCheck
import Native.Codegen.X86.Rows
import Native.Codegen.X86.Target
import Native.Data.Builder
import Native.Data.Distinct
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.Kind
import Native.Types.StringEnc

%default total

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

Prog : Decls Types.Enc.defaultEnc
Prog = MkDecls [ MkSig (nm "main") CPS [] False, MkSig (nm "f") CPS [Val] False
               , MkSig (nm "g") CPS [Val, Val] False ] []

fRef : Var (sigs Prog) (MkSig (nm "f") CPS [Val] False)
fRef = later here

gRef : Var (sigs Prog) (MkSig (nm "g") CPS [Val, Val] False)
gRef = later (later here)

------------------------------------------------------------------------------
-- Choices

||| The next number of a seed's sequence, and the seed after it
||| (splitmix64).
next : Bits64 -> (Bits64, Bits64)
next s =
  let s' = s + 0x9E3779B97F4A7C15
      z1 = prim__xor_Bits64 s' (prim__shr_Bits64 s' 30) * 0xBF58476D1CE4E5B9
      z2 = prim__xor_Bits64 z1 (prim__shr_Bits64 z1 27) * 0x94D049BB133111EB
  in (prim__xor_Bits64 z2 (prim__shr_Bits64 z2 31), s')

||| A number below `n`, from a random one: its high half scaled to `n`.
below : Bits64 -> Nat -> Nat
below r n = cast (prim__shr_Bits64 (prim__shr_Bits64 r 32 * cast n) 32)

||| One of the list, or the default when it is empty.
pick : Bits64 -> a -> List a -> a
pick r x [] = x
pick r x ys = case drop (below r (length ys)) ys of
  (y :: _) => y
  [] => x

ops : List ArithOp
ops = [Add, Sub, Mul, And, Or, Xor, Shl, Shr, Sar, DivS, DivU, RemS, RemU]

rels : List Rel
rels = [EqR, NeR, LtS, LeS, GtS, GeS, LtU, LeU, GtU, GeU]

||| Half the fuel, for each way of a fork.
halve : Nat -> Nat
halve (S (S k)) = S (halve k)
halve _ = 0

------------------------------------------------------------------------------
-- The generator

0 Code : (Ty Types.Enc.defaultEnc -> Type) -> (List (Ty Types.Enc.defaultEnc) -> Type) -> Type
Code v l = End Prog CPS False v l

0 Words : (Ty Types.Enc.defaultEnc -> Type) -> Type
Words v = List (Opnd v W64)

0 Vals : (Ty Types.Enc.defaultEnc -> Type) -> Type
Vals v = List (Opnd v Val)

||| The single operand of a list of one.
only : All (Opnd v) [t] -> Opnd v t
only [x] = x

parameters {0 v : Ty Types.Enc.defaultEnc -> Type} {0 l : List (Ty Types.Enc.defaultEnc) -> Type}

  ||| A value of those made so far.
  val : Bits64 -> Vals v -> Opnd v Val
  val r = pick r (Vx {enc = defaultEnc} 0)

  ||| A word of those made so far.
  word : Bits64 -> Words v -> Opnd v W64
  word r = pick r (W 1)

  ||| The end of a body: a value returned, or `f` or `g` called in tail
  ||| position.
  ending : Bits64 -> Vals v -> Code v l
  ending s vs =
    let (r, s1) = next s
        (a, s2) = next s1
        (b, _) = next s2
    in case below r 3 of
         0 => return (val a vs)
         1 => tailCall fRef [val a vs]
         _ => tailCall gRef [val a vs, val b vs]

  covering
  gen : Bits64 -> Nat -> Words v -> Vals v -> Code v l
  gen s Z ws vs = ending s vs
  gen s (S n) ws vs =
    let (r, s1) = next s in
    case below r 8 of
      0 => arith s1 n ws vs
      1 => box s1 n ws vs
      2 => pair s1 n ws vs
      3 => callF s1 n ws vs
      4 => callG s1 n ws vs
      5 => exit s1 n ws vs
      6 => counted s1 n ws vs
      _ => joined s1 n ws vs
    where
      -- `w = x op y`
      arith : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      arith s n ws vs = do
        let (o, s1) = next s
            (a, s2) = next s1
            (b, s3) = next s2
        w <- emit1 (Arith (pick o Add ops) (word a ws) (word b ws))
        gen s3 n (w :: ws) vs

      -- `b = box w`
      box : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      box s n ws vs = do
        let (a, s1) = next s
        b <- emit1 (AllocObj Int64H [word a ws])
        bv <- emit1 (WidenPtr b)
        gen s1 n ws (bv :: vs)

      -- `p = (u, v)`
      pair : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      pair s n ws vs = do
        let (a, s1) = next s
            (b, s2) = next s1
        p <- emit1 (AllocObj (ConH 0 2) [val a vs, val b vs])
        pv <- emit1 (WidenPtr p)
        gen s2 n ws (pv :: vs)

      -- `r = f u`
      callF : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      callF s n ws vs = do
        let (a, s1) = next s
        r <- call fRef [val a vs]
        gen s1 n ws (r :: vs)

      -- `r = g u v`
      callG : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      callG s n ws vs = do
        let (a, s1) = next s
            (b, s2) = next s1
        r <- call gRef [val a vs, val b vs]
        gen s2 n ws (r :: vs)

      -- `if x rel y then <half the rest> else <the other half>`
      exit : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      exit s n ws vs = do
        let (o, s1) = next s
            (a, s2) = next s1
            (b, s3) = next s2
            (sOut, s4) = next s3
        leaveIf (pick o EqR rels) (word a ws) (word b ws) (gen sOut (halve n) ws vs)
        gen s4 (halve n) ws vs

      -- a loop counting `i` down from a word, `acc` its accumulator, its
      -- exit the rest of the code, with `acc` among the words
      counted : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      counted s n ws vs =
        let (a, s1) = next s
            (o, s2) = next s1
            (b, s3) = next s2
        in loop [W64, W64] [word a ws, W 0] $ \go, [i, acc] => do
             leaveIf EqR i (W 0) (gen s3 n (acc :: ws) vs)
             i' <- emit1 (Arith Sub i (W 1))
             acc' <- emit1 (Arith (pick o Add ops) acc (word b (i :: ws)))
             go [i', acc']

      -- `w = if x < y then x else x + 5`
      joined : Bits64 -> Nat -> Words v -> Vals v -> Code v l
      joined s n ws vs = do
        let (a, s1) = next s
            (b, s2) = next s1
            x = word a ws
            y = word b ws
        j <- joinPoint [W64] $ \out =>
               branch LtS x y (out [x]) (do t <- emit1 (Arith Add x (W 5)); out [t])
        gen s2 n (only j :: ws) vs

------------------------------------------------------------------------------
-- What the generator made, counted from the term

record Census where
  constructor MkCensus
  operations, allocations, calls, joins, branches : Nat

Show Census where
  show c = show c.operations ++ " operations, " ++ show c.allocations ++ " allocations, "
           ++ show c.calls ++ " calls not in tail position, " ++ show c.joins
           ++ " joins (loops among them), " ++ show c.branches ++ " branches"

||| A body's constructs added to the census.
census : Body d c m ls ctx -> Census -> Census
census (Bind (AllocObj _ _) k) n = census k ({ allocations $= S } n)
census (Bind _ k) n = census k ({ operations $= S } n)
census (Join _ b r) n = census r (census b ({ joins $= S } n))
census (Branch _ _ _ a b) n = census b (census a ({ branches $= S } n))
census (Call _ _ k) n = census k ({ calls $= S } n)
census _ n = n

||| The census of the functions' bodies.
bodies : All (Def d) ss -> Census -> Census
bodies [] n = n
bodies (Defined b :: ds) n = bodies ds (census b n)
bodies (External :: ds) n = bodies ds n

------------------------------------------------------------------------------
-- The programs

||| How many steps a body takes before it ends, at most, but for forks.
fuel : Nat
fuel = 12

covering
mainB : Bits64 -> Closed Prog CPS False []
mainB s = build $ \[] => gen s fuel [] [Vx {enc = defaultEnc} 7]

covering
fB : Bits64 -> Closed Prog CPS False [Val]
fB s = build $ \[x] => gen s fuel [] [x]

covering
gB : Bits64 -> Closed Prog CPS False [Val, Val]
gB s = build $ \[x, y] => gen s fuel [] [x, y]

||| The program of a seed, its functions' bodies from three seeds of it.
covering
program : Bits64 -> Maybe (TermIR.Program.Program Types.Enc.defaultEnc Prog)
program s = do
  m <- close (mainB (3 * s))
  f <- close (fB (3 * s + 1))
  g <- close (gB (3 * s + 2))
  -- the names' distinctness decided here, as a producer decides it
  case choose (distinct (map (.name) (sigs Prog)) && distinct (map (.sym) (statics Prog))) of
    Left ok => Just (MkProgram {d = Prog} [Defined m, Defined f, Defined g] [] (MkEntry here)
                       noConIds)
    Right _ => Nothing

||| The value check's verdict on the program allocated as the code
||| generator allocates it.
verdict : TermIR.Program.Program Types.Enc.defaultEnc Prog -> Either String ()
verdict term =
  let called = callClobbers x86_64
      located = localAssign (row called) (termRow called) cycleTemp (allocRegs x86_64 term)
  in check (clobbers called) (termClobbers called) term located

||| The programs of seeds `from` to `from + k - 1`: the first refusal, or
||| the census of them all.
covering
programs : Bits64 -> Nat -> Census -> Either String Census
programs _ Z n = Right n
programs from (S k) n = case program from of
  Nothing => Left ("seed " ++ show from ++ ": the program does not close")
  Just p@(MkProgram defs _ _ _) => case verdict p of
    Left why => Left ("seed " ++ show from ++ ": " ++ why)
    Right () => programs (from + 1) k (bodies defs n)

covering
main : IO ()
main = putStrLn $ case programs 1 300 (MkCensus 0 0 0 0 0) of
  Left why => why
  Right n => "300 programs accepted, of " ++ show n
