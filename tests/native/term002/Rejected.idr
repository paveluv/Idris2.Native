-- What makes a program of the term IR well formed is its typing: each
-- block below breaks one rule, and is rejected when it is compiled, for the
-- reason its `failing` names. A producer of the IR that breaks a rule
-- therefore does not compile either, so the backend cannot emit such a
-- program.
module Rejected

import Core.Name
import Data.List
import Data.List.Quantifiers
import Data.So
import Data.Vect
import Native.Area
import Native.Codegen.IRCommon.ConIds
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty
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
import Native.Data.Distinct
import Native.HeapObj.Shape
import Native.HeapObj.ValEnc
import Native.Types.Enc
import Native.Types.Header
import Native.Types.Kind

%default total

TestEnc : Enc
TestEnc = defaultEnc

nm : String -> Name
nm s = UN (Basic s)

D : Decls TestEnc
D = MkDecls
  [ MkSig (nm "cps") CPS [Val] False
  , MkSig (nm "direct") (Direct [W64] False) [W64] False ]
  [ MkStaticSig (nm "nil") CON ]

cps : Var (sigs D) (MkSig (nm "cps") CPS [Val] False)
cps = here

direct : Var (sigs D) (MkSig (nm "direct") (Direct [W64] False) [W64] False)
direct = later here

nil : Var (statics D) (MkStaticSig (nm "nil") CON)
nil = here

------------------------------------------------------------------------------
-- Types: every operand has the type its instruction takes. `Val` is a
-- uniform value, `Fix` a fixnum, `W64` a word.

-- An operand of the wrong type.
failing "Mismatch between: Val and W64"
  negateVal : Closed D CPS False [Val]
  negateVal = build $ \[x] => do
    y <- emit1 (Unary Negate x)
    return x

-- Arithmetic on a word and a fixnum.
failing "Mismatch between: Fix and W64"
  mixed : Closed D (Direct [W64] False) False [W64]
  mixed = build $ \[x] => do
    y <- emit1 (Arith Add x (Fx {enc = TestEnc} 1))
    ret [x]

-- Arithmetic on a uniform value.
failing "Can't find an implementation for IsInt Val"
  onVal : Closed D CPS False [Val]
  onVal = build $ \[x] => do
    y <- emit1 (Arith Add x x)
    return x

-- A word narrowed as if it were a `Val`.
failing "Mismatch between: W64 and Val"
  narrowWord : Closed D (Direct [W64] False) False [W64]
  narrowWord = build $ \[x] => do
    f <- emit1 (NarrowFix {enc = TestEnc} x)
    ret [x]

-- An immediate outside the fixnum range.
failing "prim__cast_Int64Integer 4611686018427387904"
  tooBig : Closed D CPS False [Val]
  tooBig = build $ \[x] => return (Vx {enc = TestEnc} 4611686018427387904)

-- A call's arguments against its callee's parameters.
failing "Mismatch between: W64 and Val"
  wrongArgument : Closed D CPS False [Val]
  wrongArgument = build $ \[x] => tailCall cps [W 1]

-- A direct call's results against its callee's.
failing "Mismatch between: W64 and Val"
  wrongResult : Closed D (Direct [W64] False) False [W64]
  wrongResult = build $ \[x] => do
    [r] <- directCall {rs = [Val]} direct [x]
    ret [r]

-- A fixnum test needs a value.
failing "Mismatch between: All ?p [] and Vect (S ?n)"
  noValues : Closed D CPS False [Val]
  noValues = build $ \[x] => ifFixnums {enc = TestEnc} [] (\[] => return x) (return x)

-- A switch on a fixnum with a key that is not one.
failing "keysFit Fix"
  wideKey : Closed D CPS False [Val]
  wideKey = build $ \[x] => ifFixnums [x]
    (\[f] => switch f [(4611686018427387904, return x)] (return x))
    (return x)

------------------------------------------------------------------------------
-- Structure: a variable is used in scope, a jump passes what its block
-- takes, and names and switch keys are distinct.

-- A variable out of scope: no position of the empty context has a type.
failing "Mismatch between: Val :: ?xs and []"
  outOfScope : Body D CPS False [] []
  outOfScope = Return (V here)

-- A jump with arguments its block does not take.
failing "Mismatch between: Val and W64"
  wrongJump : Closed D CPS False [Val]
  wrongJump = build $ \[x] => do
    [y] <- joinPoint [W64] $ \exit => exit [x]
    return x

-- A switch's keys repeat.
failing "(mapImpl fst [(1, return x), (1, return x)])"
  sameKey : Closed D CPS False [Val]
  sameKey = build $ \[x] => switch (W 0) [(1, return x), (1, return x)] (return x)

-- A program's names repeat.
failing "MkSig (nm \"f\") CPS [] False, MkSig (nm \"f\")"
  twins : Program TestEnc (MkDecls [MkSig (nm "f") CPS [] False, MkSig (nm "f") CPS [] False] [])
  twins = MkProgram [Defined (Crash "a"), Defined (Crash "b")] [] (MkEntry here) noConIds

------------------------------------------------------------------------------
-- Conventions: a CPS function, ordinary code, returns to its continuation
-- and calls and applies with continuations; a Direct function, flat code,
-- returns its results and makes only direct calls.

-- A machine return in a CPS function.
failing "Mismatch between: Direct ?rs ?col and CPS"
  retInCPS : Closed D CPS False [Val]
  retInCPS = build $ \[x] => ret [x]

-- A CPS call in a Direct function.
failing "Mismatch between: CPS and Direct [W64] False"
  callInDirect : Closed D (Direct [W64] False) False [W64]
  callInDirect = build $ \[x] => do
    r <- call cps [Erased]
    ret [x]

-- An application in a Direct function.
failing "Mismatch between: CPS and Direct [W64] False"
  applyInDirect : Closed D (Direct [W64] False) False [W64]
  applyInDirect = build $ \[x] => do
    r <- apply Erased Erased
    ret [x]

-- A Ret of other results than the function declares.
failing "Mismatch between: [] and [W64]"
  shortRet : Closed D (Direct [W64] False) False [W64]
  shortRet = build $ \[x] => ret []

-- A CPS function is never a routine outside the program.
failing "Mismatch between: Direct ?rs ?col and CPS"
  ghost : Def D (MkSig (nm "cps") CPS [Val] False)
  ghost = External

-- A closure's code is a CPS function.
failing "Mismatch between: Direct [W64] False and CPS"
  directCode : Closed D CPS False [Val]
  directCode = build $ \[x] => do
    c <- emit1 (CodeOf direct)
    return x

------------------------------------------------------------------------------
-- Objects: what is allocated or read fits the object's kind and header:
-- a constructor's fields are uniform values, a closure's first field is its
-- code and it has fewer arguments than its arity, an array has a fill and a
-- string none, and a field is loaded as its kind has it.

-- A constructor's field that is not a `Val`.
failing "Mismatch between: W64 and Val"
  rawField : Closed D CPS False [Val]
  rawField = build $ \[x] => do
    p <- emit1 (AllocObj (ConH 0 1) [W 5])
    return x

-- A closure filled to its arity.
failing "Can't find an implementation for So False"
  fullClosure : Closed D CPS False [Val]
  fullClosure = build $ \[x] => do
    c <- emit1 (CodeOf cps)
    p <- emit1 (AllocObj (ClosureH 1 1) [c, x])
    return x

-- A closure whose code is a word: a code address is no word.
failing "Mismatch between: W64 and CodeAddr"
  wordCode : Closed D CPS False [Val]
  wordCode = build $ \[x] => do
    p <- emit1 (AllocObj (ClosureH 2 1) [W 0, x])
    return x

-- A constructor's field loaded as a word: every field of a constructor is
-- a `Val`, which the load's type must be. In Idris terms, the field of
-- `Just x` read as if it were a `Bits64`.
failing "Can't find an implementation for So False"
  rawLoad : Closed D CPS False [Val]
  rawLoad = build $ \[x] => do
    p <- emit1 (NarrowPtr CON x)
    w <- emit1 (Load W64 (MkMem (AtPtr p) Nothing 8))
    return x

-- An array without its fill.
failing "Mismatch between: Type and Opnd ?v Val"
  noFill : Closed D CPS False [Val]
  noFill = build $ \[x] => do
    p <- emit1 (AllocSized ArrayElems (W 2) ())
    return x

-- A string with a fill.
failing "Mismatch between: Opnd v Val and ()"
  stringFill : Closed D CPS False [Val]
  stringFill = build $ \[x] => do
    p <- emit1 (AllocSized StringBytes (W 2) x)
    return x

-- An object sized by a part that does not decide its size.
failing "Can't find an implementation for Sizes ConId"
  sizedById : Closed D CPS False [Val]
  sizedById = build $ \[x] => do
    p <- emit1 (AllocSized ConId (W 2) ())
    return x

-- A static used as an object of another kind.
failing "Mismatch between: CON and STRING"
  wrongKind : Closed D CPS False [Val]
  wrongKind = build $ \[x] => do
    p <- emit1 (StaticAddr nil)
    n <- emit1 (LoadPart StringBytes p)
    return x

------------------------------------------------------------------------------
-- Byte addresses: memory that holds no object is reached through a byte
-- address, which is no word. A word is no memory base, and is a byte
-- address only by a retyping (`WordToByteAddr`).

-- A load at a word.
failing "Mismatch between: W64 and ByteAddr"
  wordBase : Closed D (Direct [W64] False) False [W64]
  wordBase = build $ \[w] => do
    x <- emit1 (Load W64 (MkMem (AtBytes w) Nothing 0))
    ret [x]

-- Integer arithmetic on byte addresses: two addresses are never added. An
-- address moves by a count of bytes (`Offset`) and nothing else.
failing "Can't find an implementation for IsInt ByteAddr"
  addAddresses : Closed D (Direct [W64] False) False [W64]
  addAddresses = build $ \[w] => do
    a <- emit1 (WordToByteAddr w)
    b <- emit1 (Arith Add a a)
    ret [w]

------------------------------------------------------------------------------
-- Word/address conversion: only a function allowed to make one may turn a
-- word into an address.

-- A conversion in a function that may not make one.
failing "Mismatch between: True and False"
  convert : Closed D (Direct [W64] False) False [W64]
  convert = build $ \[x] => do
    p <- emit1 (WordToAddr CON x)
    ret [x]
