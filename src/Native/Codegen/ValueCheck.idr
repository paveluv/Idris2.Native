||| The value check (`check`), the check of what register allocation made:
||| that every location the located program reads holds the value the term
||| reads there, and that the program is one the rendering and the collector
||| can keep to. It reads the term and the located program, never the
||| allocator that made one from the other.
|||
||| The term's definitions are numbered as register allocation numbers them
||| (`Native.Codegen.RegAlloc.freshDefs`): a node's numbers when it is met,
||| before anything under it, in the order the allocation meets the nodes
||| (a join's rest before its block, a branch's yes before its no, an
||| overflow's success before its overflow), one for each value a node binds
||| or one for a node that binds none. Walking the term in that order, the
||| check learns what each operation, terminator and jump of the located
||| program must read and write, by its number (`Expected`).
|||
||| Then each block is walked from its certificate (`Block.cert`), a map of
||| what each location holds: an operation's operands must hold what the
||| term's instruction reads, an allocation's after its collection, and its
||| results then hold its values; a move copies, a value put into a location
||| is that value, and the registers a step's rendering writes besides its
||| results hold nothing after it (`clobbers`, the target's rows), nor, after
||| a collection, the GC-visible locations its `live` list leaves out, which
||| the collector does not forward. Each edge is checked against its target's
||| certificate: a jump's after its arguments become the target's parameters,
||| a branch's and an overflow's exit as they are, and a call's resume block
||| holding only what the continuation keeps: its live locations, as they were
||| at the call, and the result in the block's result register. The entry's
||| certificate is the function's parameters. So every block's certificate
||| holds on each path into it, and no fixpoint is needed.
|||
||| A definition that lowers to no operation (a retyping of a raw word, a
||| static's address held as itself) is what its operand is: its number is
||| an alias, which every content read is taken through (`canonical`).
|||
||| What the rendering and the collector rely on, besides: a register
||| written is one of the target's, by its index among those of its class
||| in the target's description; a live list, an allocation's, a direct
||| call's or a continuation's, names only locations that hold a value,
||| each at the kind of what it holds, since the rendering keeps each by
||| the kind the list gives it, the collector forwarding the GC-visible
||| ones and no other; and a resume block's parameters are its
||| continuation's live locations and then the result. A read of a location
||| that holds nothing is refused as any wrong value is, which covers a
||| register read after what overwrites it, the slow paths and a direct
||| call that keep no register among them, whose rows say they write every
||| one. A check (`Step.Check`) is a collection, and its bytes the most the
||| bumps after it in its block, up to the next check, take (`budget`): a
||| bump with no check before it in its block, or past what its check left,
||| is refused, since its memory might not be committed.
module Native.Codegen.ValueCheck

import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Pinned as IRCommon
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Cont as LocatedIR
import Native.Codegen.LocatedIR.Content as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Label as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Mem as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Step as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.RegDesc
import Native.Codegen.RegMask
import Native.Codegen.Target
import Native.Codegen.TermIR.Body as TermIR
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Def as TermIR
import Native.Codegen.TermIR.FieldTys
import Native.Codegen.TermIR.Instr as TermIR
import Native.Codegen.TermIR.Mem as TermIR
import Native.Codegen.TermIR.Opnd as TermIR
import Native.Codegen.TermIR.Program as TermIR
import Native.Codegen.TermIR.Sig as TermIR
import Native.Codegen.TermIR.Sizes as TermIR
import Native.Codegen.TermIR.StaticSig as TermIR
import Native.Codegen.TermIR.Var as TermIR

import Core.Name
import Data.List
import Data.List.Quantifiers
import Data.Singleton
import Data.SortedMap
import Data.Vect
import Data.Zippable
import Native.Data.RAList as Data
import Native.Data.Stateful as Data
import Native.HeapObj.ValEnc
import Native.Rep
import Native.Types.Enc as Types
import Native.Types.Header as Types
import Native.Types.Kind as Types

%default total

------------------------------------------------------------------------------
-- What the term says

||| What the located program must do, by the numbers of the term's
||| definitions: an operation's operands, in the order its instruction
||| lists them (`views`), and how many results it binds, the values of the
||| numbers from its own; a terminator's operands; a jump's
||| target's first parameter and its arguments; the definitions that are
||| what their operand is.
record Expected where
  constructor MkExpected
  next : Nat
  ops : SortedMap Nat (List LocatedIR.Content, Nat)
  terms : SortedMap Nat (List LocatedIR.Content)
  jumps : SortedMap Nat (Nat, List LocatedIR.Content)
  aliases : SortedMap Nat LocatedIR.Content

||| How the term walk holds a variable: a static's address held as itself,
||| in no location, as register allocation holds it; or a value in one.
data Held = Itself Name | InPlace LocatedIR.Content

HV : IRCommon.Ty enc -> Type
HV _ = Held

||| A join's label, as its first parameter's number.
LV : List (IRCommon.Ty enc) -> Type
LV _ = Nat

W : Type -> Type
W = Data.Stateful Expected Void

||| The values the definitions numbered from `n` bind, in places.
inPlace : (n : Nat) -> (ts : List (IRCommon.Ty enc)) -> All HV ts
inPlace _ [] = []
inPlace n (_ :: ts) = InPlace (LocatedIR.Content.Value n) :: inPlace (S n) ts

term : Nat -> List LocatedIR.Content -> W ()
term n os = Data.Stateful.modify { terms $= insert n os }

parameters {0 d : TermIR.Decls enc} (statics : Data.RAList Singleton d.statics)

  mutual

    ||| The term's body, numbered as register allocation numbers it, with
    ||| what each of its nodes must do.
    walk : TermIR.Body d c m ls ctx -> Data.RAList HV ctx -> Data.RAList LV ls -> W ()
    walk body env li = case body of
      TermIR.Body.Bind {ts = [IRCommon.Ty.PtrTo _]} (TermIR.Instr.StaticAddr s) k => do
        n <- numbers 1
        let name = (TermIR.Var.entry statics s).sym
        alias n (LocatedIR.Content.Put (LocatedIR.Step.StaticAddress name))
        walk k (Itself name :: env) li
      TermIR.Body.Bind (TermIR.Instr.WidenPtr (TermIR.Opnd.V x)) k =>
        case TermIR.Var.fetch x env of
          Itself s => do
            n <- numbers 1
            alias n (LocatedIR.Content.Put (LocatedIR.Step.StaticAddress s))
            walk k (Itself s :: env) li
          InPlace _ => bind (TermIR.Instr.WidenPtr (TermIR.Opnd.V x)) k env li
      TermIR.Body.Bind {ts} i k => bind i k env li
      TermIR.Body.Join ps b r => do
        first <- numbers (length ps)
        walk r env (first :: li)
        walk b (Data.RAList.prepend (inPlace first ps) env) (first :: li)
      TermIR.Body.Jump l xs => do
        n <- numbers 1
        Data.Stateful.modify { jumps $= insert n (TermIR.Var.fetch l li, contents env xs) }
      TermIR.Body.Branch _ x y a b => do
        n <- numbers 1
        term n [content env x, content env y]
        branchTo a env li
        branchTo b env li
      TermIR.Body.IfFixnums {fx} {n = n'} vs y no => do
        n <- numbers 1
        let tested = map (content env) (toList vs)
        term n tested
        first <- numbers (length vs)
        traverse_ (\(k, c) => op (first + k) [c] 1)
          (zip [0 .. length tested] tested)
        walk y (Data.RAList.prepend (inPlace first (replicate (S n') (IRCommon.Ty.Fix {enc}))) env)
          li
        branchTo no env li
      TermIR.Body.ArithOv _ x y ok ovf => do
        n <- numbers 1
        op n [content env x, content env y] 1
        walk ok (InPlace (LocatedIR.Content.Value n) :: env) li
        branchTo ovf env li
      TermIR.Body.TagOv x ok ovf => do
        n <- numbers 1
        op n [content env x] 1
        walk ok (InPlace (LocatedIR.Content.Value n) :: env) li
        branchTo ovf env li
      TermIR.Body.Switch x _ bs dflt => do
        n <- numbers 1
        term n [content env x]
        cases bs
        branchTo dflt env li
      TermIR.Body.Call _ xs k => do
        n <- numbers 1
        term n (contents env xs)
        walk k (InPlace (LocatedIR.Content.Value n) :: env) li
      TermIR.Body.TailCall _ xs => do
        n <- numbers 1
        term n (contents env xs)
      TermIR.Body.Apply f x k => do
        n <- numbers 1
        term n [content env f, content env x]
        walk k (InPlace (LocatedIR.Content.Value n) :: env) li
      TermIR.Body.TailApply f x => do
        n <- numbers 1
        term n [content env f, content env x]
      TermIR.Body.Return x => do
        n <- numbers 1
        term n [content env x]
      TermIR.Body.Enter f xs => do
        n <- numbers 1
        term n (content env f :: map (content env) xs)
      TermIR.Body.Ret xs => do
        n <- numbers 1
        term n (contents env xs)
      TermIR.Body.Crash _ => do
        n <- numbers 1
        term n []
      TermIR.Body.Unsupported _ => do
        n <- numbers 1
        term n []
      where
        ||| The numbers of the next `n` definitions, the first of them.
        numbers : Nat -> W Nat
        numbers n = Data.Stateful.state (\e => ({ next := e.next + n } e, e.next))

        ||| Where a branch goes: a block of its own, or a join's straight, its
        ||| jump numbered though no block holds it.
        branchTo : TermIR.Body d c m ls ctx -> Data.RAList HV ctx -> Data.RAList LV ls -> W ()
        branchTo (TermIR.Body.Jump _ []) _ _ = ignore (numbers 1)
        branchTo b env li = walk b env li

        cases : All (\_ => TermIR.Body d c m ls ctx) ks -> W ()
        cases [] = pure ()
        cases (b :: bs') = do branchTo b env li; cases bs'

        ||| What an operand is.
        content : Data.RAList HV ctx' -> TermIR.Opnd (TermIR.Var ctx') t -> LocatedIR.Content
        content env (TermIR.Opnd.V x) = case TermIR.Var.fetch x env of
          Itself s => LocatedIR.Content.Put (LocatedIR.Step.StaticAddress s)
          InPlace c => c
        content env (TermIR.Opnd.W i) = LocatedIR.Content.Put (LocatedIR.Step.Immediate i)
        content env (TermIR.Opnd.Fx i) = LocatedIR.Content.Put (LocatedIR.Step.Immediate i)
        content env (TermIR.Opnd.Vx i) = LocatedIR.Content.Put (LocatedIR.Step.Immediate i)
        content env TermIR.Opnd.Erased = LocatedIR.Content.Put (LocatedIR.Step.Immediate 0)

        contents : Data.RAList HV ctx' -> All (TermIR.Opnd (TermIR.Var ctx')) ts ->
                   List LocatedIR.Content
        contents env [] = []
        contents env (x :: xs) = content env x :: contents env xs

        ||| An operation's expectations, by its number.
        op : Nat -> List LocatedIR.Content -> Nat -> W ()
        op n os k = Data.Stateful.modify { ops $= insert n (os, k) }

        alias : Nat -> LocatedIR.Content -> W ()
        alias n c = Data.Stateful.modify { aliases $= insert n c }

        ||| An instruction bound in the rest: an operation, or, for one that
        ||| lowers to none, an alias of what its result is.
        bind : {ts : List (IRCommon.Ty enc)} -> TermIR.Instr d m (TermIR.Var ctx) ts ->
               TermIR.Body d c m ls (ts ++ ctx) -> Data.RAList HV ctx -> Data.RAList LV ls -> W ()
        bind i k env li = do
          n <- numbers (max 1 (length ts))
          case instrOperands env i of
            Left c => do
              alias n c
              walk k (Data.RAList.prepend (replicateAll ts (InPlace c)) env) li
            Right os => do
              op n os (length ts)
              walk k (Data.RAList.prepend (inPlace n ts) env) li
          where
            replicateAll : (us : List (IRCommon.Ty enc)) -> Held -> All HV us
            replicateAll [] _ = []
            replicateAll (_ :: us) h = h :: replicateAll us h

            ||| What an instruction of the term reads, in the order its located
            ||| instruction lists its operands (`views`); or, for one that lowers to
            ||| no operation, what its one result is (`Left`).
            instrOperands : Data.RAList HV ctx' -> TermIR.Instr d m' (TermIR.Var ctx') ts' ->
                            Either LocatedIR.Content (List LocatedIR.Content)
            instrOperands env i = case i of
              TermIR.Instr.StaticAddr s =>
                Left (LocatedIR.Content.Put
                        (LocatedIR.Step.StaticAddress (TermIR.Var.entry statics s).sym))
              TermIR.Instr.ByteAddrToWord x => Left (content env x)
              TermIR.Instr.WordToByteAddr x => Left (content env x)
              TermIR.Instr.FConst _ => Right []
              TermIR.Instr.CodeOf _ => Right []
              TermIR.Instr.AreaAddr _ => Right []
              TermIR.Instr.Offset a n => Right [content env a, content env n]
              TermIR.Instr.Arith _ x y => Right [content env x, content env y]
              TermIR.Instr.Mul128 x y => Right [content env x, content env y]
              TermIR.Instr.Div128 h l x => Right [content env h, content env l, content env x]
              TermIR.Instr.Unary _ x => Right [content env x]
              TermIR.Instr.Ext _ _ x => Right [content env x]
              TermIR.Instr.FArith _ x y => Right [content env x, content env y]
              TermIR.Instr.FNeg x => Right [content env x]
              TermIR.Instr.FSqrt x => Right [content env x]
              TermIR.Instr.FCmp _ x y => Right [content env x, content env y]
              TermIR.Instr.Convert _ x => Right [content env x]
              TermIR.Instr.Cmp _ x y => Right [content env x, content env y]
              TermIR.Instr.Load _ m => Right (memOperands env m)
              TermIR.Instr.Store _ m x => Right (content env x :: memOperands env m)
              TermIR.Instr.LoadN _ _ m => Right (memOperands env m)
              TermIR.Instr.StoreN _ m x => Right (content env x :: memOperands env m)
              TermIR.Instr.Tag x => Right [content env x]
              TermIR.Instr.Untag x => Right [content env x]
              TermIR.Instr.NarrowFix x => Right [content env x]
              TermIR.Instr.NarrowPtr _ x => Right [content env x]
              TermIR.Instr.WidenFix x => Right [content env x]
              TermIR.Instr.WidenPtr x => Right [content env x]
              TermIR.Instr.AddrToWord x => Right [content env x]
              TermIR.Instr.WordToAddr _ x => Right [content env x]
              TermIR.Instr.ValToWord x => Right [content env x]
              TermIR.Instr.WordToVal x => Right [content env x]
              TermIR.Instr.LoadHeader x => Right [content env x]
              TermIR.Instr.LoadPart _ x => Right [content env x]
              TermIR.Instr.AllocObj _ fs => Right (contents env fs)
              TermIR.Instr.AllocSized p n f => Right (content env n :: fill p f)
              TermIR.Instr.DirectCall _ xs => Right (contents env xs)
              TermIR.Instr.GetPinned _ => Right []
              TermIR.Instr.SetPinned _ x => Right [content env x]
              TermIR.Instr.SystemCall _ xs => Right (contents env xs)
              TermIR.Instr.Loc _ => Right []
              TermIR.Instr.Comment _ => Right []
              where
                fill : {0 k : Types.Kind} -> (q : Types.Header.HeaderPart k) ->
                       TermIR.Sizes.Fill (TermIR.Var ctx') q ->
                       List LocatedIR.Content
                fill Types.Header.ArrayElemsP x = [content env x]
                fill _ _ = []

                ||| A memory operand's operands: its base, then its index.
                memOperands : Data.RAList HV ctx' -> TermIR.Mem (TermIR.Var ctx') cell ->
                              List LocatedIR.Content
                memOperands env (TermIR.MkMem b i _) =
                  base b :: maybe [] (\x => [content env x]) i
                  where
                    base : TermIR.Mem.Base (TermIR.Var ctx') b' -> LocatedIR.Content
                    base (TermIR.Mem.AtBytes x) = content env x
                    base (TermIR.Mem.AtPtr x) = content env x

||| What the term says of each of its functions, by name, each made only
||| when it is asked for, so that no more than the function being checked
||| holds its own while the others are checked.
expectations : (statics : Data.RAList Singleton d.statics) -> (ss : List (TermIR.Sig enc)) ->
               All (TermIR.Def d) ss -> List (Name, () -> Expected)
expectations _ [] [] = []
expectations statics (s :: ss) (TermIR.Def.Defined b :: ds) =
  (s.name, \() => made s b) :: expectations statics ss ds
  where
    made : (s' : TermIR.Sig enc) -> TermIR.Body d s'.conv s'.converts [] s'.params -> Expected
    made s' b' =
      let start = MkExpected (length s'.params) empty empty empty empty
          (e, _) = Data.Stateful.toPair
                     (Data.Stateful.outcome start
                       (walk statics b' (Data.RAList.fromAll (inPlace 0 s'.params)) []))
      in e
expectations statics (_ :: ss) (TermIR.Def.External :: ds) = expectations statics ss ds

------------------------------------------------------------------------------
-- What the located program does

||| Where a located operand is read from: a location, or the immediate or
||| the static's address it carries.
data View : Types.Enc -> Type where
  From : LocatedIR.Location.Place enc -> View enc
  Is : LocatedIR.Content -> View enc

||| What each location holds, with the location as it was written, at the
||| type of what it holds: the registers, few, apart from the slots, so
||| that what a step writes besides its results, registers alone, is cheap
||| to forget; and the slots by number, those of a value the collector sees
||| apart from the raw ones, so that a collection, which keeps of the first
||| only those its live list names, reads the list and not every slot. A
||| slot is in one of the two. And the bytes the bumps after the last check
||| may still take (`budget`), none at a block's entry.
record State (enc : Types.Enc) where
  constructor MkState
  registers : List (LocatedIR.Location.Place enc, LocatedIR.Content)
  visible : SortedMap Nat (LocatedIR.Location.Place enc, LocatedIR.Content)
  raw : SortedMap Nat (LocatedIR.Location.Place enc, LocatedIR.Content)
  budget : Nat

namespace State

  ||| Nothing held.
  export
  none : State enc
  none = MkState [] empty empty 0

  isVisible : LocatedIR.Location.Place enc -> Bool
  isVisible p = IRCommon.Ty.gcVisible (LocatedIR.Location.Place.ty p)

  ||| What the place holds, with the place as it was written.
  export
  entry : LocatedIR.Location.Place enc -> State enc ->
          Maybe (LocatedIR.Location.Place enc, LocatedIR.Content)
  entry (LocatedIR.Location.At (LocatedIR.Location.Slot n _)) st =
    maybe (lookup n st.raw) Just (lookup n st.visible)
  entry p st = find (LocatedIR.Location.Place.same p . fst) st.registers

  ||| What the place holds.
  export
  held : LocatedIR.Location.Place enc -> State enc -> Maybe LocatedIR.Content
  held p st = map snd (entry p st)

  ||| The place holding nothing.
  export
  erased : LocatedIR.Location.Place enc -> State enc -> State enc
  erased (LocatedIR.Location.At (LocatedIR.Location.Slot n _)) st =
    case lookup n st.visible of
      Just _ => { visible $= delete n } st
      Nothing => { raw $= delete n } st
  erased p st = { registers $= filter (not . LocatedIR.Location.Place.same p . fst) } st

  ||| The place holding the content, written at the place's type.
  export
  written : LocatedIR.Location.Place enc -> LocatedIR.Content -> State enc -> State enc
  written p@(LocatedIR.Location.At (LocatedIR.Location.Slot n _)) c st =
    if isVisible p
      then { visible $= insert n (p, c), raw $= forget } st
      else { raw $= insert n (p, c), visible $= forget } st
    where
      -- the slot out of the other kind's, where it seldom is
      forget : SortedMap Nat (LocatedIR.Location.Place enc, LocatedIR.Content) ->
               SortedMap Nat (LocatedIR.Location.Place enc, LocatedIR.Content)
      forget m = maybe m (const (delete n m)) (lookup n m)
  written p c st = { registers $= ((p, c) ::) } (erased p st)

  ||| The registers of the mask holding nothing.
  export
  clobbered : RegMask -> State enc -> State enc
  clobbered m st = case st.registers of
    [] => st
    rs => { registers := filter (not . inMask . fst) rs } st
    where
      inMask : LocatedIR.Location.Place enc -> Bool
      inMask (LocatedIR.Location.At (LocatedIR.Location.Register i t)) =
        RegMask.member (IRCommon.Ty.class t) i m
      inMask _ = False

  ||| After a collection, the GC-visible locations its live list leaves out
  ||| holding nothing: the collector forwards only those it names.
  export
  collected : List (LocatedIR.Location.Place enc) -> State enc -> State enc
  collected live st =
    { registers := filter (kept . fst) st.registers,
      visible := foldl forwarded empty live } st
    where
      kept : LocatedIR.Location.Place enc -> Bool
      kept q = not (isVisible q) || any (LocatedIR.Location.Place.same q) live

      forwarded : SortedMap Nat (LocatedIR.Location.Place enc, LocatedIR.Content) ->
                  LocatedIR.Location.Place enc ->
                  SortedMap Nat (LocatedIR.Location.Place enc, LocatedIR.Content)
      forwarded m (LocatedIR.Location.At (LocatedIR.Location.Slot n _)) =
        maybe m (\x => insert n x m) (lookup n st.visible)
      forwarded m _ = m

||| Every function of the located program checked against the term it was
||| allocated from: the first refusal, if any. `clobbers` and
||| `termClobbers` are what the target's renderings write besides their
||| results (its rows).
export
check : {enc : Types.Enc} -> {d : TermIR.Decls enc} -> (clobbers : LocatedIR.Step enc -> RegMask) ->
        (termClobbers : LocatedIR.Terminator enc -> RegMask) ->
        TermIR.Program enc d -> LocatedIR.Program enc -> Either String ()
check clob tclob (TermIR.MkProgram defs _ _ _) p =
  let expected = SortedMap.fromList (expectations (Data.RAList.fromList d.statics) d.sigs defs)
      rd = p.target.allocatable
  in traverse_ (\f => case lookup f.name expected of
                        Just e => checkFunction rd clob tclob (e ()) f
                        Nothing =>
                          Left ("value check: " ++ show f.name ++ " is no function of the term"))
       p.functions
  where
    ||| A function checked against what the term says of it.
    checkFunction : RegDesc -> (clobbers : LocatedIR.Step enc -> RegMask) ->
                    (termClobbers : LocatedIR.Terminator enc -> RegMask) -> Expected ->
                    LocatedIR.Function enc -> Either String ()
    checkFunction rd clob tclob e f = do
      let blocks = SortedMap.fromList (map (\b => (b.label, b)) f.blocks)
      entry <- found ("its entry, block " ++ show f.entry) (lookup f.entry blocks)
      unless (entryHolds entry.cert f.params 0) $
        reject f.entry "the entry's certificate is not the function's parameters"
      traverse_ (block blocks) f.blocks
      where
        reject : LocatedIR.Label -> String -> Either String a
        reject l why = Left ("value check: " ++ show f.name ++ ", block " ++ show l ++ ": " ++ why)

        -- the message made only for a refusal, as `agree`'s
        found : Lazy String -> Maybe a -> Either String a
        found what = maybe (Left ("value check: " ++ show f.name ++ ": no " ++ what)) Right

        -- a location written, a register only one the target describes, by
        -- its index among those of its class
        described : LocatedIR.Label -> LocatedIR.Location.Place enc -> Either String ()
        described l p@(LocatedIR.Location.At (LocatedIR.Location.Register i t)) =
          let count = case IRCommon.Ty.class t of
                        Rep.WordClass => rd.wordCount
                        Rep.FloatClass => rd.floatCount
          in unless (i < count) $
               reject l (show p ++ " is a register the target does not describe")
        described _ _ = Right ()

        -- a live list names only locations that hold a value, each at the
        -- kind of what it holds, since the rendering keeps each by the kind
        -- the list gives it, a GC-visible one where the collector forwards
        -- it
        listsHeld : LocatedIR.Label -> Lazy String -> State enc ->
                    List (LocatedIR.Location.Place enc) -> Either String ()
        listsHeld l what st live = traverse_ one live
          where
            visible : LocatedIR.Location.Place enc -> Bool
            visible q = IRCommon.Ty.gcVisible (LocatedIR.Location.Place.ty q)

            one : LocatedIR.Location.Place enc -> Either String ()
            one p = case State.entry p st of
              Nothing => reject l (what ++ " names " ++ show p ++ ", which holds nothing")
              Just (q, _) =>
                unless (visible p == visible q) $
                  reject l
                    (what ++ " names " ++ show p ++ ", which holds a value of the other kind, "
                            ++ "written as " ++ show q)

        canonical : LocatedIR.Content -> LocatedIR.Content
        canonical c@(LocatedIR.Content.Value n) = maybe c id (lookup n e.aliases)
        canonical c = c

        entryHolds : List (LocatedIR.Content, LocatedIR.Location.Place enc) ->
                     List (LocatedIR.Location.Place enc) -> Nat -> Bool
        entryHolds [] [] _ = True
        entryHolds ((c, p) :: cs) (q :: ps) n =
          LocatedIR.Content.same c (LocatedIR.Content.Value n) && LocatedIR.Location.Place.same p q
            && entryHolds cs ps (S n)
        entryHolds _ _ _ = False

        fromCert : List (LocatedIR.Content, LocatedIR.Location.Place enc) -> State enc
        fromCert = foldl (\m, (c, p) => State.written p (canonical c) m) State.none

        holds : State enc -> LocatedIR.Content -> View enc -> Bool
        holds st c (From p) = maybe False (LocatedIR.Content.same c) (State.held p st)
        holds _ c (Is c') = LocatedIR.Content.same c c'

        -- what a step or a terminator reads, against what the term says
        agree : LocatedIR.Label -> Lazy String -> State enc -> List (View enc) ->
                List LocatedIR.Content -> Either String ()
        agree l what st vs cs =
          if length vs /= length cs
            then reject l
              (what ++ " reads " ++ show (length vs) ++ " operands, where the term reads "
                           ++ show (length cs))
            else case filter (\(v, c) => not (holds st c v)) (zip vs cs) of
              [] => Right ()
              ((v, c) :: _) =>
                reject l (what ++ " reads " ++ shown v ++ ", which does not hold " ++ show c)
          where
            shown : View enc -> String
            shown (From p) = show p
            shown (Is c') = show c'

        -- a block entered from here: its certificate holds, each value given
        -- as `given` says it, a jump's arguments as its parameters
        enters : SortedMap LocatedIR.Label (LocatedIR.Block enc) -> LocatedIR.Label -> State enc ->
                 (given : LocatedIR.Content -> Maybe LocatedIR.Content) -> LocatedIR.Label ->
                 Either String ()
        enters blocks from st given l = do
          b <- found ("block " ++ show l) (lookup l blocks)
          case filter (\(c, p) => not (holds st (want (canonical c)) (From p))) b.cert of
            [] => Right ()
            ((c, p) :: _) =>
              reject from ("block " ++ show l ++ "'s certificate has " ++ show c ++ " in " ++ show p
                           ++ ", which does not hold " ++ maybe "it" show (given c) ++ " here")
          where
            want : LocatedIR.Content -> LocatedIR.Content
            want c = maybe c id (given c)

        -- a call's resume block, entered with what its continuation keeps:
        -- each live location reloaded with what it held at the call, the
        -- call's result, of number `n`, in the block's result register; every
        -- other location the callee may have written
        resumes : SortedMap LocatedIR.Label (LocatedIR.Block enc) -> LocatedIR.Label -> State enc ->
                  Nat -> LocatedIR.Cont enc -> Either String ()
        resumes blocks from st n c = do
          b <- found ("block " ++ show c.resume) (lookup c.resume blocks)
          listsHeld from "the call's continuation" st c.live
          unless (shaped b.params c.live) $
            reject c.resume
              "a resume block's parameters are not its continuation's live locations and the result"
          let kept = foldl reload State.none c.live
              entered = maybe kept (\p => State.written p (LocatedIR.Content.Value n) kept)
                          (LocatedIR.Block.result b)
          enters blocks from entered (const Nothing) c.resume
          where
            -- a live location, reloaded with what it held at the call
            reload : State enc -> LocatedIR.Location.Place enc -> State enc
            reload m p = maybe m (\x => State.written p x m) (State.held p st)

            -- the live locations, then the result
            shaped : List (LocatedIR.Location.Place enc) -> List (LocatedIR.Location.Place enc) ->
                     Bool
            shaped [_] [] = True
            shaped (p :: ps) (q :: qs) = LocatedIR.Location.Place.same p q && shaped ps qs
            shaped _ _ = False

        at : LocatedIR.Location enc t -> View enc
        at l = From (LocatedIR.Location.At l)

        opnd : LocatedIR.Opnd enc t -> View enc
        opnd (LocatedIR.Opnd.R l) = From (LocatedIR.Location.At l)
        opnd (LocatedIR.Opnd.Imm i) = Is (LocatedIR.Content.Put (LocatedIR.Step.Immediate i))
        opnd (LocatedIR.Opnd.StaticRef s) =
          Is (LocatedIR.Content.Put (LocatedIR.Step.StaticAddress s))

        args : List (LocatedIR.Opnd.Arg enc) -> List (View enc)
        args = map (\(LocatedIR.Opnd.MkArg o) => opnd o)

        ||| An instruction's operands, in the order `Instr.operands` lists them, its
        ||| immediates and statics included.
        views : LocatedIR.Instr enc -> List (View enc)
        views i = case i of
          LocatedIR.Instr.Offset _ x y => [opnd x, opnd y]
          LocatedIR.Instr.Arith _ _ x y => [opnd x, opnd y]
          LocatedIR.Instr.Mul128 _ _ x y => [opnd x, opnd y]
          LocatedIR.Instr.Div128 _ _ h l x => [opnd h, opnd l, opnd x]
          LocatedIR.Instr.Unary _ _ x => [at x]
          LocatedIR.Instr.ArithOv _ _ x y _ => [opnd x, opnd y]
          LocatedIR.Instr.Ext _ _ _ x => [at x]
          LocatedIR.Instr.FArith _ _ x y => [at x, at y]
          LocatedIR.Instr.FNeg _ x => [at x]
          LocatedIR.Instr.FSqrt _ x => [at x]
          LocatedIR.Instr.FCmp _ _ x y => [at x, at y]
          LocatedIR.Instr.Convert _ _ x => [at x]
          LocatedIR.Instr.Cmp _ _ x y => [opnd x, opnd y]
          LocatedIR.Instr.Load _ _ m => mem m
          LocatedIR.Instr.Store _ m x => at x :: mem m
          LocatedIR.Instr.LoadN _ _ _ m => mem m
          LocatedIR.Instr.StoreN _ m x => at x :: mem m
          LocatedIR.Instr.Tag _ x => [at x]
          LocatedIR.Instr.Untag _ x => [at x]
          LocatedIR.Instr.TagOv _ x _ => [at x]
          LocatedIR.Instr.Narrow _ _ x => [at x]
          LocatedIR.Instr.Widen _ x => [at x]
          LocatedIR.Instr.AddrToWord _ x => [at x]
          LocatedIR.Instr.WordToAddr _ _ x => [at x]
          LocatedIR.Instr.ValToWord _ x => [at x]
          LocatedIR.Instr.WordToVal _ x => [at x]
          LocatedIR.Instr.LoadHeader _ x => [at x]
          LocatedIR.Instr.LoadPart _ _ x => [at x]
          LocatedIR.Instr.AllocObj _ _ fs _ => args fs
          LocatedIR.Instr.AllocSized _ _ count fill _ => at count :: maybe [] (\o => [opnd o]) fill
          LocatedIR.Instr.DirectCall _ xs _ _ _ => args xs
          LocatedIR.Instr.SetPinned _ x => [opnd x]
          LocatedIR.Instr.SystemCall _ xs => map opnd xs
          _ => []
          where
            mem : LocatedIR.Mem enc -> List (View enc)
            mem m = From (LocatedIR.Mem.place m.base) :: maybe [] (\i => [at i]) m.index

        ||| The block an operation may leave to, an overflow's.
        side : LocatedIR.Instr enc -> Maybe LocatedIR.Label
        side (LocatedIR.Instr.ArithOv _ _ _ _ l) = Just l
        side (LocatedIR.Instr.TagOv _ _ l) = Just l
        side _ = Nothing

        step : SortedMap LocatedIR.Label (LocatedIR.Block enc) -> LocatedIR.Label -> State enc ->
               LocatedIR.Step enc -> Either String (State enc)
        step blocks l st s@(LocatedIR.Step.Op d i) = do
          (os, k) <- found
            ("definition " ++ show d ++ ", of operation " ++ LocatedIR.Instr.instrName i)
                        (lookup d e.ops)
          let collecting = LocatedIR.Instr.collecting i
              clobbered = State.clobbered (clob s) st
              after = maybe clobbered (\live => State.collected live clobbered) collecting
          whenJust collecting $ listsHeld l ("operation [" ++ show d ++ "]'s live list") st
          -- an allocation reads its operands after its collection
          agree l ("operation [" ++ show d ++ "] " ++ LocatedIR.Instr.instrName i)
            (if LocatedIR.Instr.isAllocation i then after else st) (views i) os
          let ps = LocatedIR.Instr.results i
          unless (length ps == k) $
            reject l ("operation [" ++ show d ++ "] writes " ++ show (length ps)
                      ++ " results, where the term binds " ++ show k)
          traverse_ (described l) ps
          -- a bump past a check takes from the bytes it left
          bumped <- case i of
            LocatedIR.Instr.AllocObj _ h _ Nothing => do
              let n = 8 * Types.Header.objectWords h
              unless (n <= after.budget) $
                reject l ("operation [" ++ show d ++ "] bumps " ++ show n ++ " bytes "
                          ++ (if after.budget == 0 then "with no check before it in its block"
                                else "where its check left " ++ show after.budget))
              pure ({ budget := minus after.budget n } after)
            _ => pure after
          -- an overflow leaves before the results are written
          whenJust (side i) $ \to =>
            enters blocks l (foldl (flip State.erased) bumped ps) (const Nothing) to
          pure (results d ps bumped)
          where
            -- the results, the values of the numbers from the operation's
            results : Nat -> List (LocatedIR.Location.Place enc) -> State enc -> State enc
            results _ [] st' = st'
            results j (p :: ps') st' =
              results (S j) ps' (State.written p (LocatedIR.Content.Value j) st')
        -- a check: where a collection can start, its budget at most the
        -- allocation margin, for the bumps after it
        step _ l st s@(LocatedIR.Step.Check n live) = do
          unless (LocatedIR.Instr.withinMargin n) $
            reject l ("a check for " ++ show n ++ " bytes, past the allocation margin")
          listsHeld l "a check's live list" st live
          pure ({ budget := n } (State.collected live (State.clobbered (clob s) st)))
        step _ l st (LocatedIR.Step.Move d x) = do
          let to = LocatedIR.Location.At d
          described l to
          pure (maybe (State.erased to st) (\c => State.written to c st)
                      (State.held (LocatedIR.Location.At x) st))
        step _ l st (LocatedIR.Step.Remat d m) = do
          described l (LocatedIR.Location.At d)
          pure (State.written (LocatedIR.Location.At d) (LocatedIR.Content.Put m) st)
        step _ l st (LocatedIR.Step.Par cs) = do
          let read = map (\(LocatedIR.Step.MkCopy d x) =>
                            (LocatedIR.Location.At d, State.held (LocatedIR.Location.At x) st)) cs
          traverse_ (described l . fst) read
          pure (foldl (\m, (to, c) => maybe (State.erased to m) (\c' => State.written to c' m) c)
                  st read)

        ||| A terminator's operands, in the order `Terminator.termOperands` lists
        ||| them, its immediates and statics included.
        termViews : LocatedIR.Terminator enc -> List (View enc)
        termViews t = case t of
          LocatedIR.Terminator.IfFixnums rs _ _ => map at rs
          LocatedIR.Terminator.Branch _ x y _ _ => [opnd x, opnd y]
          LocatedIR.Terminator.Switch r _ _ => [at r]
          LocatedIR.Terminator.Call _ xs _ => args xs
          LocatedIR.Terminator.TailCall _ xs => args xs
          LocatedIR.Terminator.Apply f x _ => [at f, at x]
          LocatedIR.Terminator.TailApply f x => [at f, at x]
          LocatedIR.Terminator.Return x => [opnd x]
          LocatedIR.Terminator.Enter f xs => at f :: map opnd xs
          LocatedIR.Terminator.Ret xs => args xs
          _ => []

        ||| The blocks a terminator branches or jumps to: not a call's resume
        ||| block, which its continuation enters.
        targets : LocatedIR.Terminator enc -> List LocatedIR.Label
        targets t = case t of
          LocatedIR.Terminator.Jump l => [l]
          LocatedIR.Terminator.IfFixnums _ y n => [y, n]
          LocatedIR.Terminator.Branch _ _ _ y n => [y, n]
          LocatedIR.Terminator.Switch _ cs d => map snd cs ++ [d]
          _ => []

        block : SortedMap LocatedIR.Label (LocatedIR.Block enc) -> LocatedIR.Block enc ->
                Either String ()
        block blocks b = do
          traverse_ (described b.label . snd) b.cert
          st <- foldlM (step blocks b.label) (fromCert b.cert) b.body
          let n = b.node
              st' = State.clobbered (tclob b.term) st
          case b.term of
            LocatedIR.Terminator.Jump l => do
              (first, xs) <- found ("jump " ++ show n) (lookup n e.jumps)
              enters blocks b.label st' (argument first xs) l
            t => do
              os <- found ("terminator " ++ show n) (lookup n e.terms)
              agree b.label (LocatedIR.Terminator.termName t) st (termViews t) os
              traverse_ (enters blocks b.label st' (const Nothing)) (targets t)
              whenJust (LocatedIR.Terminator.termCont t) (resumes blocks b.label st n)
          where
            -- a jump's target's parameter, numbered from `first`, as its argument
            argument : Nat -> List LocatedIR.Content -> LocatedIR.Content -> Maybe LocatedIR.Content
            argument first xs (LocatedIR.Content.Value v) =
              if v >= first then getAt (minus v first) xs else Nothing
            argument _ _ _ = Nothing
