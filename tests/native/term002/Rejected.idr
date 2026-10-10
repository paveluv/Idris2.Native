module Rejected

import Compiler.Native.TermIR.Build

%default total

TestEnc : Enc
TestEnc = defaultEnc

nm : String -> Name
nm s = UN (Basic s)

D : Decls TestEnc
D = MkDecls
  [ MkSig (nm "cps") InCPS [Val] False
  , MkSig (nm "direct") (InDirect [W64] False) [W64] False ]
  [ MkStaticSig (nm "nil") CON ]

cps : Var (sigs D) (MkSig (nm "cps") InCPS [Val] False)
cps = here

direct : Var (sigs D) (MkSig (nm "direct") (InDirect [W64] False) [W64] False)
direct = later here

nil : Var (statics D) (MkStaticSig (nm "nil") CON)
nil = here

------------------------------------------------------------------------------
-- Rule 1: types

-- An operand of the wrong type.
failing "Mismatch between: Val and W64"
  negateVal : Closed D InCPS False [Val]
  negateVal = build $ \[x] => do
    y <- emit1 (Unary Negate x)
    return x

-- Arithmetic on a word and a fixnum.
failing "Mismatch between: Fix and W64"
  mixed : Closed D (InDirect [W64] False) False [W64]
  mixed = build $ \[x] => do
    y <- emit1 (Arith Add x (Fx {enc = TestEnc} 1))
    ret [x]

-- Arithmetic on a uniform value.
failing "Can't find an implementation for IsInt Val"
  onVal : Closed D InCPS False [Val]
  onVal = build $ \[x] => do
    y <- emit1 (Arith Add x x)
    return x

-- A word narrowed as if it were a `Val`.
failing "Mismatch between: W64 and Val"
  narrowWord : Closed D (InDirect [W64] False) False [W64]
  narrowWord = build $ \[x] => do
    f <- emit1 (NarrowFix {enc = TestEnc} x)
    ret [x]

-- An immediate outside the fixnum range.
failing "prim__cast_Int64Integer 4611686018427387904"
  tooBig : Closed D InCPS False [Val]
  tooBig = build $ \[x] => return (Vx {enc = TestEnc} 4611686018427387904)

-- A call's arguments against its callee's parameters.
failing "Mismatch between: W64 and Val"
  wrongArgument : Closed D InCPS False [Val]
  wrongArgument = build $ \[x] => tailCall cps [W 1]

-- A direct call's results against its callee's.
failing "Mismatch between: W64 and Val"
  wrongResult : Closed D (InDirect [W64] False) False [W64]
  wrongResult = build $ \[x] => do
    [r] <- directCall {rs = [Val]} direct [x]
    ret [r]

-- A fixnum test needs a value.
failing "Mismatch between: All ?p [] and Vect (S ?n)"
  noValues : Closed D InCPS False [Val]
  noValues = build $ \[x] => ifFixnums {enc = TestEnc} [] (\[] => return x) (return x)

-- A switch on a fixnum with a key that is not one.
failing "keysFit Fix"
  wideKey : Closed D InCPS False [Val]
  wideKey = build $ \[x] => ifFixnums [x]
    (\[f] => switch f [(4611686018427387904, return x)] (return x))
    (return x)

------------------------------------------------------------------------------
-- Rule 2: structure

-- A variable out of scope: no position of the empty context has a type.
failing "Mismatch between: Val :: ?xs and []"
  outOfScope : Body D InCPS False [] []
  outOfScope = Return (V here)

-- A jump with arguments its block does not take.
failing "Mismatch between: Val and W64"
  wrongJump : Closed D InCPS False [Val]
  wrongJump = build $ \[x] => do
    [y] <- joinPoint [W64] $ \exit => exit [x]
    return x

-- A switch's keys repeat.
failing "distinct (mapImpl fst [(1, return x), (1, return x)])"
  sameKey : Closed D InCPS False [Val]
  sameKey = build $ \[x] => switch (W 0) [(1, return x), (1, return x)] (return x)

-- A program's names repeat.
failing "So (distinct (mapImpl .name"
  twins : Program TestEnc (MkDecls [MkSig (nm "f") InCPS [] False, MkSig (nm "f") InCPS [] False] [])
  twins = MkProgram [Defined (Crash "a"), Defined (Crash "b")] [] (MkEntry here) noConIds

------------------------------------------------------------------------------
-- Rule 3: conventions

-- A machine return in a CPS function.
failing "Mismatch between: InDirect ?rs ?col and InCPS"
  retInCPS : Closed D InCPS False [Val]
  retInCPS = build $ \[x] => ret [x]

-- A CPS call in a Direct function.
failing "Mismatch between: InCPS and InDirect [W64] False"
  callInDirect : Closed D (InDirect [W64] False) False [W64]
  callInDirect = build $ \[x] => do
    r <- call cps [Erased]
    ret [x]

-- An application in a Direct function.
failing "Mismatch between: InCPS and InDirect [W64] False"
  applyInDirect : Closed D (InDirect [W64] False) False [W64]
  applyInDirect = build $ \[x] => do
    r <- apply Erased Erased
    ret [x]

-- A Ret of other results than the function declares.
failing "Mismatch between: [] and [W64]"
  shortRet : Closed D (InDirect [W64] False) False [W64]
  shortRet = build $ \[x] => ret []

-- A CPS function is never a routine outside the program.
failing "Mismatch between: InDirect ?rs ?col and InCPS"
  ghost : Def D (MkSig (nm "cps") InCPS [Val] False)
  ghost = External

-- A closure's code is a CPS function.
failing "Mismatch between: InDirect [W64] False and InCPS"
  directCode : Closed D InCPS False [Val]
  directCode = build $ \[x] => do
    c <- emit1 (CodeAddr direct)
    return x

------------------------------------------------------------------------------
-- Rule 6: objects

-- A constructor's field that is not a `Val`.
failing "Mismatch between: W64 and Val"
  rawField : Closed D InCPS False [Val]
  rawField = build $ \[x] => do
    p <- emit1 (AllocObj (ConH 0 1) [W 5])
    return x

-- A closure filled to its arity.
failing "Can't find an implementation for So False"
  fullClosure : Closed D InCPS False [Val]
  fullClosure = build $ \[x] => do
    p <- emit1 (AllocObj (ClosureH 1 1) [W 0, x])
    return x

-- An array without its fill.
failing "Mismatch between: Type and Opnd ?v Val"
  noFill : Closed D InCPS False [Val]
  noFill = build $ \[x] => do
    p <- emit1 (AllocSized ArrayElems (W 2) ())
    return x

-- A string with a fill.
failing "Mismatch between: Opnd v Val and ()"
  stringFill : Closed D InCPS False [Val]
  stringFill = build $ \[x] => do
    p <- emit1 (AllocSized StringBytes (W 2) x)
    return x

-- An object sized by a part that does not decide its size.
failing "Can't find an implementation for Sizes ConId"
  sizedById : Closed D InCPS False [Val]
  sizedById = build $ \[x] => do
    p <- emit1 (AllocSized ConId (W 2) ())
    return x

-- A static used as an object of another kind.
failing "Mismatch between: CON and STRING"
  wrongKind : Closed D InCPS False [Val]
  wrongKind = build $ \[x] => do
    p <- emit1 (StaticAddr nil)
    n <- emit1 (LoadPart StringBytes p)
    return x

------------------------------------------------------------------------------
-- Rule 8: word/address conversion

-- A conversion in a function that may not make one.
failing "Mismatch between: True and False"
  convert : Closed D (InDirect [W64] False) False [W64]
  convert = build $ \[x] => do
    p <- emit1 (WordToAddr CON x)
    ret [x]
