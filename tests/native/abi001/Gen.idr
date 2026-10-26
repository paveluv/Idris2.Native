-- Values passed as the ABI places them (Native.Codegen.Target.place): a
-- Direct function of nineteen values, alternately a word and a double, more
-- than either register file holds, returns them rotated by one, so that its
-- results land elsewhere than its arguments. The caller checks every result
-- and exits with 42, or with 1 + the index of the first wrong one. Both are
-- written with the builder (Native.Codegen.TermIR.Build), and so is the
-- `exit` the caller ends with, a system call as the runtime's is. A crash
-- jumps to the runtime's `crash`, the entry calls the runtime's `start`,
-- and a continuation's allocation may call its `allocSlow`, which the
-- program defines itself, under the names the runtime contract gives them.
--
-- A Direct function is how a flat function is compiled: a machine function
-- whose arguments and results are its registers' values. `spread` is as a
-- flat function of nineteen arguments, `Bits64` and `Double` in turn, would
-- be, returning nineteen values. x86-64 has six word argument registers and
-- eight double ones; what does not fit goes in the per-thread area ARGS,
-- never on the machine stack, so that a call of any arity, a tail call
-- included, is moves and a jump. Results come back the same way.
module Main

import Core.Name
import Core.Name.Namespace
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Native.Codegen.ELF
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Link
import Native.Codegen.Linkage.Areas
import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.LocatedIR.Program
import Native.Codegen.RegAlloc
import Native.Codegen.Target
import Native.Codegen.TermIR.Body
import Native.Codegen.TermIR.Build
import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Def
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd
import Native.Codegen.TermIR.Program
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.StaticDef
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var
import Native.Codegen.X86.Encode
import Native.Codegen.X86.Render
import Native.Codegen.X86.Target
import Native.Data.Distinct
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.Port
import Native.Primitive
import Native.Rep
import Native.Routine
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.IntegerRoutine
import Native.Types.StringEnc
import Native.Types.StringRoutine
import System.File

%default total

TestEnc : Enc
TestEnc = MkEnc FixnumTag1 (MkBignumEnc Limb64 SignMagnitude) Utf8

nm : String -> Name
nm s = NS (mkNamespace "Main") (UN (Basic s))

count : Nat
count = 19

isWord : Nat -> Bool
isWord Z = True
isWord (S i) = not (isWord i)

tyOf : Nat -> Ty TestEnc
tyOf i = if isWord i then W64 else F64

||| The value of argument i: 1000 + i for a word, 2000 + i for a double.
value : Nat -> Int64
value i = cast (if isWord i then 1000 + i else 2000 + i)

||| Result j is argument j + 1, the last argument last but one.
source : Nat -> Nat
source j = if S j == count then 0 else S j

indices : List Nat
indices = [0 .. minus count 1]

Params : List (Ty TestEnc)
Params = map tyOf indices

Results : List (Ty TestEnc)
Results = map (tyOf . source) indices

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

D : Decls TestEnc
D = MkDecls [ MkSig (nm "main") CPS [] False
            , MkSig (nm "spread") (Direct Results False) Params False
            , MkSig (nm "exit") (Direct [] False) [W64] False
            , MkSig (flatName runtimeCrash) (Direct [] False) [W64, W64] False
            , MkSig (flatName runtimeStart) (Direct [] False) [W64, W64] False
            , MkSig (flatName runtimeAllocSlow) (Direct [W64] False) [W64] False ]
            []

spreadRef : Var (sigs D) (MkSig (nm "spread") (Direct Results False) Params False)
spreadRef = later here

exitRef : Var (sigs D) (MkSig (nm "exit") (Direct [] False) [W64] False)
exitRef = later (later here)

||| The runtime's `start`, reduced to what this program needs: the first
||| allocation window, mapped, of `window` bytes, as the allocation pointer
||| and its limit. The stack limit stays 0, so the stack is not checked.
startBody : Closed D (Direct [] False) False [W64, W64]
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
allocSlowBody : Closed D (Direct [W64] False) False [W64]
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

||| The runtime's `crash`: the message, `length` bytes at `message`, written
||| to the standard error, then the process ended with status 1.
crashBody : Closed D (Direct [] False) False [W64, W64]
crashBody = build $ \[message, length] => do
  _ <- emit1 (SystemCall 6 [W 1, W 2, message, length, W 0, W 0, W 0])
  _ <- emit1 (SystemCall 6 [W 231, W 1, W 0, W 0, W 0, W 0, W 0])
  ret []

||| The system call exit_group with the status.
exitBody : Closed D (Direct [] False) False [W64]
exitBody = build $ \[status] => do
  _ <- emit1 (SystemCall 6 [W 231, status, W 0, W 0, W 0, W 0, W 0])
  ret []

||| The arguments, rotated by one: what `spread` returns.
rotate : All p (x :: xs) -> All p (xs ++ [x])
rotate (y :: ys) = go ys y
  where
    go : All p zs -> p x -> All p (zs ++ [x])
    go [] z = [z]
    go (w :: ws) z = w :: go ws z

spreadBody : Closed D (Direct Results False) False Params
spreadBody = build $ \args => ret (rotate args)

||| Argument i: a word, or a double converted from one.
argument : (i : Nat) -> Build D CPS False v l (Opnd v (tyOf i))
argument i with (isWord i)
  _ | True = pure (W (value i))
  _ | False = emit1 (Convert I2F (W (value i)))

arguments : (is : List Nat) -> Build D CPS False v l (All (Opnd v) (map Main.tyOf is))
arguments [] = pure []
arguments (i :: is) = [| argument i :: arguments is |]

exitWith : Int64 -> End D CPS False v l
exitWith status = do
  _ <- directCall exitRef [W status]
  crash "exit returned"

||| Result j checked against the argument it should be: a double through
||| its conversion back to a word.
result : (j : Nat) -> Opnd v (tyOf (source j)) -> End D CPS False v l -> End D CPS False v l
result j r next with (isWord (source j))
  _ | True = branch EqR r (W (value (source j))) next (exitWith (cast (1 + j)))
  _ | False = do
    w <- emit1 (Convert F2I r)
    branch EqR w (W (value (source j))) next (exitWith (cast (1 + j)))

results : (js : List Nat) -> All (Opnd v) (map (Main.tyOf . Main.source) js) -> End D CPS False v l
results [] [] = exitWith 42
results (j :: js) (r :: rs) = result j r (results js rs)

mainBody : Closed D CPS False []
mainBody = build $ \[] => do
  args <- arguments indices
  rs <- directCall spreadRef args
  results indices rs

classOfIndex : Nat -> RegClass
classOfIndex i = class (tyOf i)

covering
main : IO ()
main = do
  putStrLn "arguments:"
  traverse_ (\(i, l) => putStrLn ("  " ++ show i ++ " " ++ show (tyOf i) ++ ": " ++ show l))
            (zip indices (place x86_64.abi (map classOfIndex indices)))
  putStrLn "results:"
  traverse_
    (\(j, l) => putStrLn ("  " ++ show j ++ " " ++ show (tyOf (source j)) ++ ": " ++ show l))
            (zip indices (place x86_64.abi (map (classOfIndex . source) indices)))
  let Just m = close mainBody | Nothing => putStrLn "main: a level outside its context"
  let Just s = close spreadBody | Nothing => putStrLn "spread: a level outside its context"
  let Just e = close exitBody | Nothing => putStrLn "exit: a level outside its context"
  let Just cr = close crashBody | Nothing => putStrLn "crash: a level outside its context"
  let Just st = close startBody | Nothing => putStrLn "start: a level outside its context"
  let Just al = close allocSlowBody | Nothing => putStrLn "allocSlow: a level outside its context"
  case choose (distinct (map (.name) (sigs D)) && distinct (map (.sym) (statics D))) of
    Right _ => putStrLn "names repeat"
    Left ok => do
      let ir =
            allocRegs x86_64
              (MkProgram {d = D}
                [Defined m, Defined s, Defined e, Defined cr, Defined st, Defined al] []
               (MkEntry here) noConIds)
      let Right rendered = render TestEnc realised [] ir
        | Left err => putStrLn ("render: " ++ err)
      let Right image = linkProgram TestEnc windowBytes rendered.areas rendered.text rendered.rodata
        | Left problems => putStrLn ("link: " ++ show problems)
      Right () <- writeImage "abi" image
        | Left err => putStrLn ("write: " ++ show err)
      putStrLn ("ARGS words: " ++ show rendered.areas.args)
