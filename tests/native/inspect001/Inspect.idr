-- The inspection gate: elaborator scripts read the constructors of every
-- type the backend gives a hand-written instance or an encoding table, and
-- the checks test what the instance promises. A hand-written `Eq` that ends
-- in `_ == _ = False` stays silently wrong when a constructor is added, and
-- coverage checking cannot notice; the gate does. Tests may use elaborator
-- reflection, the compiler's own source does not.
--
-- The gate checks itself: the type `Broken` has an `Eq`, a `Show`, a table
-- and its inverse, each wrong in one place, and every check must report it.
module Main

import Data.Fin
import Data.List
import Language.Reflection
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned
import Native.Codegen.IRCommon.Ty
import Native.Codegen.Linkage.Sym
import Native.Codegen.Platform
import Native.Codegen.Target
import Native.Codegen.X86.Asm
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.Kind
import Native.Types.StringRoutine
import System

%language ElabReflection
%default covering

------------------------------------------------------------------------------
-- Enumerating a type's constructors

||| A value to apply a constructor to, per argument type. A constructor whose
||| argument type has no instance stops the gate from building.
interface Sample a where
  sample : a

Sample Nat where
  sample = 0

Sample (Fin (S n)) where
  sample = FZ

Sample Bool where
  sample = False

Sample (List a) where
  sample = []

Sample Kind where
  sample = CON

Sample Arch where
  sample = X86_64

Sample OS where
  sample = Linux

||| The fully qualified name a short name refers to; `getCons` needs one.
resolve : Name -> Elab Name
resolve n = do
  [(n', _)] <- getType n
    | _ => fail "\{show n} is not exactly one name"
  pure n'

explicitArgs : TTImp -> Nat
explicitArgs (IPi _ _ ExplicitArg _ _ sc) = S (explicitArgs sc)
explicitArgs (IPi _ _ _ _ _ sc) = explicitArgs sc
explicitArgs _ = Z

baseName : Name -> String
baseName (NS _ n) = baseName n
baseName (UN (Basic s)) = s
baseName n = show n

str : String -> TTImp
str s = IPrimVal EmptyFC (Str s)

||| A pair of terms. Tuple syntax inside a quotation does not lift its
||| unquotes out, so the pair's constructor is written in prefix form.
pair : TTImp -> TTImp -> TTImp
pair x y = `(MkPair ~(x) ~(y))

||| Each constructor of the type, with its name, applied to `sample` for
||| every explicit argument, and passed to `wrap`.
constructors : (wrap : TTImp -> TTImp) -> Name -> Elab TTImp
constructors wrap ty = do
  cons <- getCons !(resolve ty)
  entries <- for cons $ \c => do
    [(c', t)] <- getType c
      | _ => fail "\{show c} is ambiguous"
    let v = foldl (\f, _ => `(~(f) sample)) (IVar EmptyFC c') (replicate (explicitArgs t) ())
    pure (pair (str (baseName c')) (wrap v))
  pure (foldr (\x, acc => `(~(x) :: ~(acc))) `([]) entries)

||| Every constructor of a type, as values: `[("CON", CON), …]`.
enumerate : {a : Type} -> Name -> Elab (List (String, a))
enumerate ty = check !(constructors id ty)

||| Every constructor of an indexed family, as the strings its `Show` gives.
shows : Name -> Elab (List (String, String))
shows ty = check !(constructors (\v => `(show ~(v))) ty)

------------------------------------------------------------------------------
-- The checks, in plain Idris

||| An enumeration that found no constructors would make every other check
||| pass vacuously.
nonEmpty : String -> List a -> List String
nonEmpty ty [] = ["\{ty}: no constructors found"]
nonEmpty ty _ = []

||| Each value equals itself and differs from every other constructor's.
eqFailures : Eq a => String -> List (String, a) -> List String
eqFailures ty vs =
  [ "\{ty}: \{n} is not equal to itself" | (n, v) <- vs, not (v == v) ] ++
  [ "\{ty}: \{n} equals \{m}" | (n, v) <- vs, (m, w) <- vs, n /= m, v == w ]

||| Distinct constructors show differently.
distinct : String -> String -> List (String, String) -> List String
distinct ty what vs =
  [ "\{ty}: \{n} and \{m} \{what} \{show s}"
  | ((n, s), i) <- zip vs [0 .. length vs], ((m, t), j) <- zip vs [0 .. length vs], i < j, s == t ]

showFailures : Show a => String -> List (String, a) -> List String
showFailures ty vs = distinct ty "both show as" (map (\(n, v) => (n, show v)) vs)

||| An encoding table gives distinct constructors distinct codes.
tableFailures : Show b => String -> (a -> b) -> List (String, a) -> List String
tableFailures ty f vs = distinct ty "both have the code" (map (\(n, v) => (n, show (f v))) vs)

||| An inverse table gives back the constructor each code came from.
inverseFailures : Eq a => String -> (a -> b) -> (b -> Maybe a) -> List (String, a) -> List String
inverseFailures ty f g vs =
  [ "\{ty}: \{n} does not come back from its code" | (n, v) <- vs, g (f v) /= Just v ]

------------------------------------------------------------------------------
-- The gate checks itself

data Broken = A | B | C

Eq Broken where
  A == A = True
  B == B = True
  _ == _ = False            -- C was added after the catch-all

Show Broken where
  show A = "A"
  show B = "B"
  show C = "B"              -- a copied line

brokenCode : Broken -> Nat
brokenCode A = 0
brokenCode B = 1
brokenCode C = 1            -- a copied line

brokenDecode : Nat -> Maybe Broken
brokenDecode 0 = Just A
brokenDecode 1 = Just B
brokenDecode _ = Nothing

------------------------------------------------------------------------------
-- What is gated

kinds : List (String, Kind)
kinds = %runElab enumerate `{Kind}

-- Under an encoding with fixnums, where every constructor exists.
TestEnc : Enc
TestEnc = { val := FixnumTag1 } defaultEnc

tys : List (String, Ty TestEnc)
tys = %runElab enumerate `{Ty}

convs : List (String, Conv TestEnc)
convs = %runElab enumerate `{Conv}

lowerings : List (String, Lowering)
lowerings = %runElab enumerate `{Lowering}

encodings : List (String, ValEnc)
encodings = %runElab enumerate `{ValEnc}

arithOps : List (String, ArithOp)
arithOps = %runElab enumerate `{ArithOp}

stringRoutines : List (String, StringRoutine)
stringRoutines = %runElab enumerate `{StringRoutine}

pinnedNames : List (String, Pinned)
pinnedNames = %runElab enumerate `{Pinned}

parts : List (String, String)
parts = %runElab shows `{HeaderPart}

regs : List (String, Reg64)
regs = %runElab enumerate `{Reg64}

xmms : List (String, Xmm)
xmms = %runElab enumerate `{Xmm}

conds : List (String, Cond)
conds = %runElab enumerate `{Cond}

aluOps : List (String, AluOp)
aluOps = %runElab enumerate `{AluOp}

shiftOps : List (String, ShiftOp)
shiftOps = %runElab enumerate `{ShiftOp}

sseOps : List (String, SseOp)
sseOps = %runElab enumerate `{SseOp}

widths : List (String, Width)
widths = %runElab enumerate `{Width}

syms : List (String, Sym)
syms = %runElab enumerate `{Sym}

brokens : List (String, Broken)
brokens = %runElab enumerate `{Broken}

arches : List (String, Arch)
arches = %runElab enumerate `{Arch}

oses : List (String, OS)
oses = %runElab enumerate `{OS}

||| A record has one constructor, so its gate is every combination of its
||| fields' constructors, written here.
platforms : List (String, Platform)
platforms = [ (show a ++ "-" ++ show o, MkPlatform a o) | (_, a) <- arches, (_, o) <- oses ]

||| The types whose hand-written `Eq` the gate checks. The test's `run`
||| compares this list with the `Eq` instances in the backend's source.
gatedEq : List String
gatedEq = ["Arch", "Conv", "Kind", "Lowering", "OS", "Platform", "Reg64", "StringRoutine", "Ty", "ValEnc"]

failures : List String
failures = concat
  [ nonEmpty "Kind" kinds, nonEmpty "Ty" tys, nonEmpty "Conv" convs
  , nonEmpty "Lowering" lowerings, nonEmpty "ArithOp" arithOps, nonEmpty "Pinned" pinnedNames
  , nonEmpty "HeaderPart" parts, nonEmpty "Reg64" regs, nonEmpty "Xmm" xmms, nonEmpty "Cond" conds
  , nonEmpty "AluOp" aluOps, nonEmpty "ShiftOp" shiftOps, nonEmpty "SseOp" sseOps
  , nonEmpty "Width" widths, nonEmpty "Sym" syms, nonEmpty "ValEnc" encodings
  , nonEmpty "Broken" brokens, nonEmpty "Arch" arches, nonEmpty "OS" oses
  , eqFailures "Arch" arches, eqFailures "OS" oses, eqFailures "Platform" platforms
  , showFailures "Arch" arches, showFailures "OS" oses, showFailures "Platform" platforms
  , inverseFailures "parsePlatform" show parsePlatform platforms
  , eqFailures "Kind" kinds, eqFailures "Ty" tys
  , eqFailures "Conv" convs, eqFailures "Lowering" lowerings, eqFailures "Reg64" regs
  , eqFailures "ValEnc" encodings, showFailures "ValEnc" encodings
  , eqFailures "StringRoutine" stringRoutines
  , showFailures "Kind" kinds, distinct "HeaderPart" "both show as" parts
  , showFailures "ArithOp" arithOps, showFailures "Conv" convs, showFailures "Ty" tys
  , showFailures "Pinned" pinnedNames, showFailures "Reg64" regs
  , showFailures "Xmm" xmms, showFailures "Cond" conds, showFailures "AluOp" aluOps
  , showFailures "ShiftOp" shiftOps, showFailures "SseOp" sseOps, showFailures "Width" widths
  , tableFailures "code" code kinds, inverseFailures "kindOfCode" code kindOfCode kinds
  , tableFailures "regNum" regNum regs, tableFailures "xmmNum" xmmNum xmms
  , tableFailures "condCode" condCode conds, tableFailures "aluDigit" aluDigit aluOps
  , tableFailures "shiftDigit" shiftDigit shiftOps, tableFailures "sseOpcode" sseOpcode sseOps
  , tableFailures "symLabel" symLabel syms, tableFailures "symName" symName syms
  , eqFailures "Broken" brokens, showFailures "Broken" brokens
  , tableFailures "brokenCode" brokenCode brokens
  , inverseFailures "brokenDecode" brokenCode brokenDecode brokens
  ]

main : IO ()
main = do
  args <- getArgs
  if "--gated" `elem` args
     then traverse_ putStrLn gatedEq
     else do
       traverse_ putStrLn failures
       putStrLn "gated Eq: \{unwords gatedEq}"
