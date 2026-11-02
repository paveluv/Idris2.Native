-- The value check (`Native.Codegen.ValueCheck`): that every location the
-- located program reads holds the value the term reads there. The term is
-- the specification, and the check reads it alongside what register
-- allocation made of it, never the allocator itself.
--
-- The program, written by hand in the term IR, is as the Idris
--
--     main : a
--     main = let w = 3 + 4 in
--            let r = count 7 in      -- not a tail call: `w` lives across it
--            if w == 7 then r else count r
--
--     count : a -> a
--     count x = go 3 0
--       where
--         go : Bits64 -> Bits64 -> a
--         go 0 _ = x
--         go i acc = go (i - 1) (acc + 1)
--
--     pair : a -> (a, Int)
--     pair x = (x, 5)            -- 5 boxed, then the pair: `x` lives
--                                -- across the box's allocation
--
--     inc : Bits64 -> Bits64     -- a Direct function, which a machine
--     inc n = n + 1              -- call reaches
--
--     bump : a -> a
--     bump x = let w = 3 + 4 in
--              if w + inc w == 0 then x else x   -- `w` lives across the
--                                                -- direct call
--
-- `go` a loop: a join, a block with parameters, which jumps back to itself
-- passing the next counter and accumulator at once.
--
-- Allocated as the code generator allocates it (a slot for every value,
-- then each operation's operands moved into the registers its rendering
-- reads them in), it is accepted. Then the located IR is changed, each
-- change a mistake an allocator that keeps values in registers could
-- make, and each must be refused. They are written against the located
-- IR as allocated, which `count`'s loop body, its block 3, is:
--
--     0  reg0 := slot1              the counter, i
--     1  reg0 := Sub reg0, #1       i - 1
--     2  slot3 := reg0
--     3  reg0 := slot2              the accumulator, acc
--     4  reg0 := Add reg0, #1       acc + 1
--     5  slot4 := reg0
--     6  ...                        the jump's arguments into slot1, slot2
--
-- with block 1, the loop's head, holding i in slot1 and acc in slot2; and
-- `main`'s block 0 computes w into reg0, saves it in slot0 and calls
-- `count`, the call's continuation keeping slot0 live, and its resume
-- block, 1, reloads w from slot0 into reg0 to compare it; `pair`'s
-- allocations each list what is live across them, x in slot0 among them,
-- for the collector to forward; and `bump`'s block 0 computes w into reg0,
-- saves it in slot1, calls `inc`, and reloads w from slot1 into reg0 (its
-- step 3) for the sum.
--
-- The mistakes come in two sorts: a location holding the wrong value where
-- it is read; and, last, a located program the rendering or the collector
-- could not keep to at all: a slot read that nothing wrote, a live list
-- naming what holds nothing or naming it at the other kind (a word for a
-- value the collector must see), a resume block whose parameters are not
-- its continuation's and the result, a join entered from a block that did
-- not write what it reads, a value left in a register across an allocation
-- or a direct call, which no register survives, and a register the target
-- does not have.
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
import Native.Codegen.LocatedIR.Block
import Native.Codegen.LocatedIR.Cont
import Native.Codegen.LocatedIR.Content
import Native.Codegen.LocatedIR.Function
import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Label
import Native.Codegen.LocatedIR.Location
import Native.Codegen.LocatedIR.Opnd
import Native.Codegen.LocatedIR.Program
import Native.Codegen.LocatedIR.Step
import Native.Codegen.LocatedIR.Terminator
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
Prog = MkDecls [ MkSig (nm "main") CPS [] False, MkSig (nm "count") CPS [Val] False
               , MkSig (nm "pair") CPS [Val] False
               , MkSig (nm "inc") (Direct [W64] False) [W64] False
               , MkSig (nm "bump") CPS [Val] False ] []

countRef : Var (sigs Prog) (MkSig (nm "count") CPS [Val] False)
countRef = later here

incRef : Var (sigs Prog) (MkSig (nm "inc") (Direct [W64] False) [W64] False)
incRef = later (later (later here))

||| The entry, `main`: `w` computed before the call to `count` and read
||| after it.
mainBody : Closed Prog CPS False []
mainBody = build $ \[] => do
  w <- emit1 (Arith Add (W 3) (W 4))
  r <- call countRef [Vx {enc = defaultEnc} 7]
  leaveIf EqR w (W 7) (return r)
  tailCall countRef [r]

||| `count x`: the loop `go`, of a counter from 3 and an accumulator from
||| 0, returns `x` at 0; otherwise it goes on with the counter less one and
||| the accumulator plus one.
countBody : Closed Prog CPS False [Val]
countBody = build $ \[x] =>
  loop [W64, W64] [W 3, W 0] $ \go, [i, acc] => do
    leaveIf EqR i (W 0) (return x)
    i' <- emit1 (Arith Sub i (W 1))
    acc' <- emit1 (Arith Add acc (W 1))
    go [i', acc']

||| `pair x`, `(x, 5)`: 5 boxed, then the pair allocated, `x` live across
||| the box's allocation, which may collect.
pairBody : Closed Prog CPS False [Val]
pairBody = build $ \[x] => do
  b <- emit1 (AllocObj Int64H [W 5])
  bv <- emit1 (WidenPtr b)
  p <- emit1 (AllocObj (ConH 0 2) [x, bv])
  pv <- emit1 (WidenPtr p)
  return pv

||| `inc n`, `n + 1`, a Direct function: a machine call reaches it, and it
||| returns its result in a register.
incBody : Closed Prog (Direct [W64] False) False [W64]
incBody = build $ \[n] => do
  m <- emit1 (Arith Add n (W 1))
  ret [m]

||| The single operand of a list of one.
only : All p [t] -> p t
only [x] = x

||| `bump x`: `w` computed before a direct call of `inc` and read after it.
bumpBody : Closed Prog CPS False [Val]
bumpBody = build $ \[x] => do
  w <- emit1 (Arith Add (W 3) (W 4))
  r <- directCall incRef [w]
  s <- emit1 (Arith Add w (only r))
  leaveIf EqR s (W 0) (return x)
  return x

0 Located : Type
Located = LocatedIR.Program.Program Types.Enc.defaultEnc

0 Steps : Type
Steps = List (LocatedIR.Step.Step Types.Enc.defaultEnc)

0 Cert : Type
Cert = List (Content, Place Types.Enc.defaultEnc)

||| The program with block `l` of the function named `f` changed.
changed : String -> Nat -> (Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc) ->
          Located -> Located
changed f l g p = { functions $= map fn } p
  where
    blk : Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
    blk b@(MkBlock l' _ _ _ _ _) = if l == l' then g b else b

    fn : Function Types.Enc.defaultEnc -> Function Types.Enc.defaultEnc
    fn h = if h.name == nm f then { blocks $= map blk } h else h

||| A block with its steps changed.
steps : (Steps -> Steps) -> Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
steps f (MkBlock l ps cert body t n) = MkBlock l ps cert (f body) t n

||| A block with its certificate changed.
certificate : (Cert -> Cert) -> Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
certificate f (MkBlock l ps cert body t n) = MkBlock l ps (f cert) body t n

||| Block 3 of `count`, the loop's body, with its steps changed.
body : (Steps -> Steps) -> Located -> Located
body f = changed "count" 3 (steps f)

||| The steps with step `i` replaced by those given.
at : Nat -> Steps -> Steps -> Steps
at i ns ss = take i ss ++ ns ++ drop (S i) ss

||| The steps with step `i` and the one after it in each other's places.
swap : Nat -> Steps -> Steps
swap i ss = case drop i ss of
  (a :: b :: rest) => take i ss ++ b :: a :: rest
  _ => ss

||| A word register.
reg : Nat -> Location Types.Enc.defaultEnc W64
reg i = Register i W64

||| A word slot.
slot : Nat -> Location Types.Enc.defaultEnc W64
slot n = Slot n W64

||| The certificate with its locations' values swapped where it holds the
||| first location's and the second's.
crossed : (a, b : Location Types.Enc.defaultEnc W64) -> Cert -> Cert
crossed a b cert = case (lookup a, lookup b) of
  (Just x, Just y) => map (swapped x y) cert
  _ => cert
  where
    lookup : Location Types.Enc.defaultEnc W64 -> Maybe Content
    lookup l = map fst (find (\(_, q) => Place.same q (At l)) cert)

    swapped : Content -> Content -> (Content, Place Types.Enc.defaultEnc) ->
              (Content, Place Types.Enc.defaultEnc)
    swapped x y (c, q) =
      if Place.same q (At a) then (y, q) else if Place.same q (At b) then (x, q) else (c, q)

||| The certificate with what it says the first location holds said of the
||| second instead.
moved : (a, b : Location Types.Enc.defaultEnc W64) -> Cert -> Cert
moved a b = map (\(c, q) => if Place.same q (At a) then (c, At b) else (c, q))

||| A block ending in a call, the call's continuation keeping nothing live.
keepsNothing : Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
keepsNothing (MkBlock l ps cert body (LocatedIR.Terminator.Call f xs (MkCont r _)) n) =
  MkBlock l ps cert body (LocatedIR.Terminator.Call f xs (MkCont r [])) n
keepsNothing b = b

||| A block with its parameters changed.
params : (List (Place Types.Enc.defaultEnc) -> List (Place Types.Enc.defaultEnc)) ->
         Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
params f (MkBlock l ps cert body t n) = MkBlock l (f ps) cert body t n

||| A block with its allocations' live lists changed.
lists : (List (Place Types.Enc.defaultEnc) -> List (Place Types.Enc.defaultEnc)) ->
        Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
lists f = steps (map relist)
  where
    relist : LocatedIR.Step.Step Types.Enc.defaultEnc -> LocatedIR.Step.Step Types.Enc.defaultEnc
    relist (Op d (LocatedIR.Instr.AllocObj r h fs live)) =
      Op d (LocatedIR.Instr.AllocObj r h fs (f live))
    relist st = st

||| Slot 0, a `Val`'s, named as a word's.
asWord : Place Types.Enc.defaultEnc -> Place Types.Enc.defaultEnc
asWord (At (Slot 0 _)) = At (slot 0)
asWord q = q

||| A block whose operation [3], the pair's allocation, reads `x` from
||| register 1, moved there from slot0 before the box's allocation, and
||| lists it there.
viaRegister : Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
viaRegister = steps (\ss => Move (Register 1 Val) (Slot 0 Val) :: map moved ss)
  where
    arg : Arg Types.Enc.defaultEnc -> Arg Types.Enc.defaultEnc
    arg (MkArg (R (Slot 0 t))) = MkArg (R (Register 1 t))
    arg a = a

    place : Place Types.Enc.defaultEnc -> Place Types.Enc.defaultEnc
    place (At (Slot 0 t)) = At (Register 1 t)
    place q = q

    moved : LocatedIR.Step.Step Types.Enc.defaultEnc -> LocatedIR.Step.Step Types.Enc.defaultEnc
    moved (Op 3 (LocatedIR.Instr.AllocObj r h fs live)) =
      Op 3 (LocatedIR.Instr.AllocObj r h (map arg fs) (map place live))
    moved st = st

||| A block with its allocations' live lists leaving out the GC-visible
||| locations, as if none were live there.
unrooted : Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
unrooted = steps (map forget)
  where
    forget : LocatedIR.Step.Step Types.Enc.defaultEnc -> LocatedIR.Step.Step Types.Enc.defaultEnc
    forget (Op d (LocatedIR.Instr.AllocObj r h fs live)) =
      Op d (LocatedIR.Instr.AllocObj r h fs (filter (not . gcVisible . Place.ty) live))
    forget st = st

||| A block with each allocation's live list leaving out the allocation's
||| own fields, as if it read them before its collection.
fieldsUnlisted : Block Types.Enc.defaultEnc -> Block Types.Enc.defaultEnc
fieldsUnlisted = steps (map forget)
  where
    forget : LocatedIR.Step.Step Types.Enc.defaultEnc -> LocatedIR.Step.Step Types.Enc.defaultEnc
    forget (Op d (LocatedIR.Instr.AllocObj r h fs live)) =
      let own = opsRegs fs [] in
      Op d (LocatedIR.Instr.AllocObj r h fs (filter (\p => not (any (Place.same p) own)) live))
    forget st = st

||| The steps with each parallel move of two from slots given its sources
||| swapped, each read at its own destination's type.
argsSwapped : Steps -> Steps
argsSwapped = map swapped
  where
    swapped : LocatedIR.Step.Step Types.Enc.defaultEnc -> LocatedIR.Step.Step Types.Enc.defaultEnc
    swapped (Par [MkCopy d1 (Slot n1 t1), MkCopy d2 (Slot n2 t2)]) =
      Par [MkCopy d1 (Slot n2 t1), MkCopy d2 (Slot n1 t2)]
    swapped st = st

||| The check's verdict on a located program of the term, the call's
||| clobbers those given.
verdict : TermIR.Program.Program Types.Enc.defaultEnc Prog -> RegMask -> String -> Located ->
          IO ()
verdict term called what p =
  let v = check (clobbers called) (termClobbers called) term p in
  putStrLn (what ++ ": " ++ either id (const "accepted") v)

||| The program allocated, then local assignment's moves into registers.
assigned : TermIR.Program.Program Types.Enc.defaultEnc Prog -> Located
assigned term =
  let called = callClobbers x86_64 in
  localAssign (row called) (termRow called) cycleTemp (allocRegs x86_64 term)

||| The verdicts on the program as allocated and on each mistake.
verdicts : TermIR.Program.Program Types.Enc.defaultEnc Prog -> IO ()
verdicts term = do
  verdict term (callClobbers x86_64) "as allocated" (assigned term)
  -- the accumulator's load reading the counter's slot: the Add reads i
  verdict term (callClobbers x86_64) "a load from the wrong slot"
    (body (at 3 [Move (reg 0) (slot 1)]) (assigned term))
  -- the accumulator's load left out: the Add reads i - 1, still in reg0
  verdict term (callClobbers x86_64) "a load left out" (body (at 3 []) (assigned term))
  -- i - 1 saved after its register is loaded with acc: slot3, and then
  -- slot1, the loop's next counter, has acc
  verdict term (callClobbers x86_64) "a register reused before it is saved"
    (body (swap 2) (assigned term))
  -- reg0 written between the counter's load and the Sub that reads it
  verdict term (callClobbers x86_64) "a register overwritten before its use"
    (body (at 0 [Move (reg 0) (slot 1), Remat (reg 0) (Immediate 99)]) (assigned term))
  -- the loop's head said to hold acc in slot1 and i in slot2
  verdict term (callClobbers x86_64) "a certificate with the counter and accumulator crossed"
    (changed "count" 1 (certificate (crossed (slot 1) (slot 2))) (assigned term))
  -- before the local assignment, which makes the jump's parallel move
  -- moves: the loop's next counter passed as its accumulator, and the
  -- next accumulator as its counter
  verdict term (callClobbers x86_64) "the jump's arguments swapped"
    (body argsSwapped (allocRegs x86_64 term))
  -- `w` taken, after the call, from reg0, where the Add left it, the
  -- resume block's certificate saying so and its reload from slot0 left
  -- out; but the callee may write every register
  verdict term (callClobbers x86_64) "a value kept in a register across a call"
    (changed "main" 1 (steps (drop 1) . certificate (moved (slot 0) (reg 0))) (assigned term))
  -- `w` left out of the call's continuation, as if it were dead there,
  -- and so out of its resume block's parameters
  verdict term (callClobbers x86_64) "a live value left out of a continuation"
    (changed "main" 1 (params (drop 1)) (changed "main" 0 keepsNothing (assigned term)))
  -- `x` left out of the box's allocation's live list: the collector, which
  -- forwards only what it lists, may leave its slot stale
  verdict term (callClobbers x86_64) "a live value left out of an allocation's live list"
    (changed "pair" 0 unrooted (assigned term))
  -- the pair's own fields left out of its allocation's live list: the
  -- object is initialised from them after the collection
  verdict term (callClobbers x86_64) "an allocation's fields left out of its live list"
    (changed "pair" 0 fieldsUnlisted (assigned term))
  -- the counter's load from slot9, which nothing writes
  verdict term (callClobbers x86_64) "a read of a slot nothing wrote"
    (body (at 0 [Move (reg 0) (slot 9)]) (assigned term))
  -- the allocations' live lists naming slot9 too
  verdict term (callClobbers x86_64) "a live list naming a slot nothing wrote"
    (changed "pair" 0 (lists (At (Slot 9 Val) ::)) (assigned term))
  -- x's slot listed as a word's: the collector would not forward it
  verdict term (callClobbers x86_64) "a live list naming a value as a word"
    (changed "pair" 0 (lists (map asWord)) (assigned term))
  -- the resume block's parameters, w's slot and the result's, reversed
  verdict term (callClobbers x86_64) "a resume block's parameters out of their order"
    (changed "main" 1 (params reverse) (assigned term))
  -- the entry's store of the accumulator's 0 left out: the loop's head is
  -- entered from there without it, and from the loop's body with it
  verdict term (callClobbers x86_64) "a join entered from a block that did not write its value"
    (changed "count" 0 (steps (at 3 [])) (assigned term))
  -- x in register 1 across the box's allocation, whose slow path keeps
  -- no register
  verdict term (callClobbers x86_64) "a value in a register across an allocation"
    (changed "pair" 0 viaRegister (assigned term))
  -- w's reload after the call to `inc` left out: the sum reads it from
  -- reg0, which the callee may write
  verdict term (callClobbers x86_64) "a value in a register across a direct call"
    (changed "bump" 0 (steps (at 3 [])) (assigned term))
  -- the counter loaded into register 99, which x86-64 does not have
  verdict term (callClobbers x86_64) "a register the target does not have"
    (body (at 0 [Move (Register 99 W64) (slot 1)]) (assigned term))

covering
main : IO ()
main = do
  let Just m = close mainBody | Nothing => putStrLn "main: a level outside its context"
  let Just c = close countBody | Nothing => putStrLn "count: a level outside its context"
  let Just pr = close pairBody | Nothing => putStrLn "pair: a level outside its context"
  let Just inc = close incBody | Nothing => putStrLn "inc: a level outside its context"
  let Just bump = close bumpBody | Nothing => putStrLn "bump: a level outside its context"
  -- the names' distinctness decided here, as a producer decides it
  case choose (distinct (map (.name) (sigs Prog)) && distinct (map (.sym) (statics Prog))) of
    Left ok =>
      verdicts (MkProgram {d = Prog} [Defined m, Defined c, Defined pr, Defined inc, Defined bump]
                  [] (MkEntry here) noConIds)
    Right _ => putStrLn "names repeat"
