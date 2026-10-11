||| The term IR: the native backend's IR as a typed, scoped term.
|||
||| What makes an IR well formed, for types, scoping, conventions and
||| objects, is a typing rule here, so a producer that breaks one does not
||| compile:
||| * An instruction binds its results. A variable is a position in the
|||   context with an erased proof of its type there (`Var`), so it is
|||   defined before it is used, has one type, and is never redefined; a
|||   reference costs one word.
||| * A block is a join point bound in scope (`Join`). A label is a variable
|||   of the label context, whose entries are the blocks' parameter types,
|||   so every jump names a block in scope and supplies its parameters.
||| * A call's continuation is the body under it, so a resume point cannot be
|||   entered any other way, and what is live across the call is the free
|||   variables of that body: no live list exists to be wrong.
||| * A callee, a code address and a static are variables of the program's
|||   declarations (`Decls`), so each matches its declaration: a call its
|||   callee's convention, parameters and results; a static's address its
|||   kind. A routine outside the program is Direct, and a CPS function is
|||   always of the program.
||| * The convention indexes the body: `Ret` exists only in a Direct body
|||   and returns its declared results; `Return`, `Call`, `TailCall`, `Apply`
|||   and `TailApply` only in a CPS one. A second index, whether the function
|||   may convert between words and addresses, is the only way to
|||   `AddrToWord` and `WordToAddr`; the producer decides it from the
|||   function's module.
||| * What must be decided is decided where the term is made, and the term
|||   keeps the evidence: an immediate encodes as its type, a switch's keys
|||   are distinct (and fixnums, on a `Fix`), a header's parts fit their bits
|||   and a closure has fewer arguments filled than its arity, the program's
|||   names are distinct.
|||
||| What stays the producer's claim is what it is in the IR: `NarrowFix` and
||| `NarrowPtr`, the range of a word given to `Tag`, a field's offset in a
||| load or a store.
|||
||| The term is the input of `Compiler.Native.RegAlloc`, which turns it into
||| the IR, computing every live list. Producers build it through
||| `Compiler.Native.TermIR.Build`.
module Compiler.Native.TermIR

import public Core.FC
import public Core.Name
import public Compiler.Native.IRCommon
import public Data.List
import public Data.List.Quantifiers
import public Data.So
import public Data.Vect

%default total

------------------------------------------------------------------------------
-- Variables

||| That the list has the value at the position, counted from its front.
public export
data AtIndex : Nat -> a -> List a -> Type where
  First : AtIndex Z x (x :: xs)
  Later : AtIndex n x xs -> AtIndex (S n) x (y :: xs)

||| A variable of a context: its position, with the erased proof that the
||| context has a value of the type there. At run time it is the position
||| alone.
public export
record Var (xs : List a) (x : a) where
  constructor MkVar
  index : Nat
  0 at : AtIndex index x xs

||| The variable just bound.
public export
here : Var (x :: xs) x
here = MkVar 0 First

||| A variable under one more binding.
public export
later : Var xs x -> Var (y :: xs) x
later (MkVar i at) = MkVar (S i) (Later at)

||| What an environment holds for the variable.
public export
fetch : Var xs x -> All p xs -> p x
fetch (MkVar i at) env = go i at env
  where
    go : (i : Nat) -> (0 _ : AtIndex i y ys) -> All p ys -> p y
    go Z First (z :: _) = z
    go (S i) (Later at) (_ :: zs) = go i at zs

||| The entry a variable names: a callee's signature, a static's.
public export
entry : (xs : List a) -> Var xs x -> a
entry xs (MkVar i at) = go i xs at
  where
    go : (i : Nat) -> (ys : List a) -> (0 _ : AtIndex i y ys) -> a
    go Z (z :: _) First = z
    go (S i) (_ :: zs) (Later at) = go i zs at

||| The variable at the position, if the context has the type there.
public export
varAt : DecEq a => (i : Nat) -> (x : a) -> (xs : List a) -> Maybe (Var xs x)
varAt Z x (y :: ys) = case decEq x y of
  Yes Refl => Just here
  No _ => Nothing
varAt (S i) x (_ :: ys) = map later (varAt i x ys)
varAt _ _ [] = Nothing

||| Every entry of a list with its variable, in one pass: the proofs are
||| erased, so building them costs nothing at run time.
public export
enumerate : (xs : List a) -> List (x ** Var xs x)
enumerate xs = go 0 xs (\p => p)
  where
    -- How a position in a suffix of `xs` is one in `xs`.
    0 Into : Nat -> List a -> Type
    Into i rest = {y : a} -> {j : Nat} -> AtIndex j y rest -> AtIndex (i + j) y xs

    0 step : {i : Nat} -> {0 z : a} -> {0 zs : List a} -> Into i (z :: zs) -> Into (S i) zs
    step f {y} {j} p = replace {p = \n => AtIndex n y xs} (sym (plusSuccRightSucc i j)) (f (Later p))

    go : (i : Nat) -> (rest : List a) -> (0 _ : Into i rest) -> List (x ** Var xs x)
    go i [] _ = []
    go i (y :: ys) f =
      (y ** MkVar i (replace {p = \n => AtIndex n y xs} (plusZeroRightNeutral i) (f First))) :: go (S i) ys (step f)

-- Merge sort, public so that `distinct` reduces on a literal list where a
-- proof about one is searched for.
public export
mergeSorted : Ord a => List a -> List a -> List a
mergeSorted [] ys = ys
mergeSorted xs [] = xs
mergeSorted (x :: xs) (y :: ys) = if x <= y then x :: mergeSorted xs (y :: ys) else y :: mergeSorted (x :: xs) ys

public export
halves : List a -> (List a, List a)
halves [] = ([], [])
halves [x] = ([x], [])
halves (x :: y :: zs) = let (as, bs) = halves zs in (x :: as, y :: bs)

||| The list, sorted.
public export
sorted : Ord a => List a -> List a
sorted [] = []
sorted [x] = [x]
sorted xs = let (as, bs) = halves xs in assert_total (mergeSorted (sorted as) (sorted bs))

||| Whether no element repeats: a switch's keys, a program's names. It sorts,
||| so it is quick on the thousands of names of a program.
public export
distinct : Ord a => List a -> Bool
distinct xs = apart (sorted xs)
  where
    apart : List a -> Bool
    apart (x :: y :: zs) = x /= y && apart (y :: zs)
    apart _ = True

------------------------------------------------------------------------------
-- Declarations

||| A function's convention. A Direct function declares its results, and
||| whether a call of it may start a collection.
public export
data Conv : Enc -> Type where
  InCPS : Conv enc
  InDirect : (results : List (Ty enc)) -> (collects : Bool) -> Conv enc

||| What a caller knows of a function.
public export
record Sig (enc : Enc) where
  constructor MkSig
  name : Name
  conv : Conv enc
  params : List (Ty enc)
  ||| Whether the function may convert between words and addresses, which
  ||| only the functions of the module implementing the runtime's memory
  ||| interface may: no word can be derived from a pointer elsewhere, which
  ||| is what lets the rooting stubs cover every pointer there is.
  converts : Bool

||| What a reference knows of a static object.
public export
record StaticSig where
  constructor MkStaticSig
  sym : Name
  kind : Kind

||| The program's declarations: its functions, and the runtime's routines
||| it calls, and its statics.
public export
record Decls (enc : Enc) where
  constructor MkDecls
  sigs : List (Sig enc)
  statics : List StaticSig

------------------------------------------------------------------------------
-- Types of operations

||| The integer types: arithmetic, comparisons and switches take two of one.
public export
data IsInt : Ty enc -> Type where
  IntW : IsInt W64
  IntF : {auto 0 fx : HasFixnums enc.val} -> IsInt (Fix {enc} {fx})

||| What a conversion takes.
public export
convFrom : ConvOp -> Ty enc
convFrom I2F = W64
convFrom F2I = F64
convFrom FBits = F64
convFrom BitsF = W64

||| What a conversion makes.
public export
convTo : ConvOp -> Ty enc
convTo I2F = F64
convTo F2I = W64
convTo FBits = W64
convTo BitsF = F64

||| The operations that have an overflow form.
public export
data OvOp = OvAdd | OvSub | OvMul

public export
ovArith : OvOp -> ArithOp
ovArith OvAdd = Add
ovArith OvSub = Sub
ovArith OvMul = Mul

||| The types of an object's fields, from its header: a closure's code
||| address and its filled arguments; a double's bits; a raw object's words.
public export
fieldTys : {0 k : Kind} -> Header enc k -> List (Ty enc)
fieldTys (ConH _ a) = replicate a Val
fieldTys (ClosureH _ f) = W64 :: replicate f Val
fieldTys Int64H = [W64]
fieldTys DoubleH = [F64]
fieldTys (StringH n) = replicate (byteWords n) W64
fieldTys (BignumH _ n) = replicate n W64
fieldTys IORefH = [Val]
fieldTys (ArrayH n) = replicate n Val
fieldTys (BufferH n) = replicate (byteWords n) W64
fieldTys PtrH = [W64]

||| A header the IR may allocate: its parts fit their bits, and a closure has
||| fewer arguments filled than its arity.
public export
wellFormed : {0 k : Kind} -> Header enc k -> Bool
wellFormed h@(ClosureH arity filled) = fits h && filled < arity
wellFormed h = fits h

||| The parts that alone decide an object's size.
public export
data Sizes : HeaderPart k -> Type where
  SizesArray : Sizes ArrayElems
  SizesString : Sizes StringBytes
  SizesBuffer : Sizes BufferBytes

||| Whether the keys of a switch on the type are its values: a `Fix`'s are
||| fixnums.
public export
keysFit : Ty enc -> List Int64 -> Bool
keysFit (Fix {fx}) ks = all (\k => inFixnumRange (cast k)) ks
keysFit _ _ = True

------------------------------------------------------------------------------
-- Operands, memory references and instructions, over any variables

||| An operand: a variable, or an immediate that encodes as its type.
public export
data Opnd : (var : Ty enc -> Type) -> Ty enc -> Type where
  V : var t -> Opnd var t
  ||| A word.
  W : Int64 -> Opnd var W64
  ||| A fixnum, as a `Fix`.
  Fx : {auto 0 fx : HasFixnums enc.val} ->
       (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd var (Fix {enc})
  ||| A fixnum, as a `Val`.
  Vx : {auto 0 fx : HasFixnums enc.val} ->
       (i : Int64) -> {auto 0 ok : So (inFixnumRange (cast i))} -> Opnd var Val
  ||| The erased value, as a `Val`, under every encoding.
  Erased : Opnd var Val

||| What fills a new object of a run-time size, by the part that sizes it: a
||| `Val` for every element of an `ARRAY`, which the collector scans;
||| nothing for the raw kinds, whose bytes are left as they are. A part that
||| sizes nothing (`Sizes` has no proof for it) takes nothing.
public export
Fill : (Ty enc -> Type) -> HeaderPart k -> Type
Fill var ArrayElems = Opnd var Val
Fill var StringBytes = ()
Fill var BufferBytes = ()
Fill var ConId = ()
Fill var ConArity = ()
Fill var ClosureArity = ()
Fill var ClosureFilled = ()
Fill var BignumNegative = ()
Fill var BignumWords = ()

||| A memory reference's base: an object pointer or a raw address, never a
||| `Val`, which may be a fixnum.
public export
data Base : (var : Ty enc -> Type) -> Type where
  AtWord : Opnd var W64 -> Base var
  AtPtr : Opnd var (PtrTo k) -> Base var

||| A memory reference: a base, an optional index counting units of the
||| access's width, and a constant byte offset.
public export
record Mem {enc : Enc} (var : Ty enc -> Type) where
  constructor MkMem
  base : Base var
  index : Maybe (Opnd var W64)
  offset : Int

||| An instruction of a function that may (`True`) or may not convert between
||| words and addresses, with the types of the results it binds.
public export
data Instr : Decls enc -> Bool -> (var : Ty enc -> Type) -> List (Ty enc) -> Type where
  FConst : Double -> Instr d m var [F64]
  ||| The entry address of a CPS function of the program: a closure's code.
  CodeAddr : Var d.sigs (MkSig n InCPS ps cv) -> Instr d m var [W64]
  ||| The address of a static object, as a pointer to its kind.
  StaticAddr : Var d.statics (MkStaticSig s k) -> Instr d m var [PtrTo k]
  AreaAddr : Area -> Instr d m var [W64]
  ||| Integer arithmetic on two `W64`s or two `Fix`es; on `Fix`es the
  ||| producer guarantees the result is a fixnum.
  Arith : {auto 0 int : IsInt t} -> ArithOp -> Opnd var t -> Opnd var t -> Instr d m var [t]
  Unary : UnOp -> Opnd var W64 -> Instr d m var [W64]
  ||| Narrow a word to the width, then extend it back, signed or not.
  Ext : SubWord -> (signed : Bool) -> Opnd var W64 -> Instr d m var [W64]
  FArith : FOp -> Opnd var F64 -> Opnd var F64 -> Instr d m var [F64]
  FNeg : Opnd var F64 -> Instr d m var [F64]
  ||| Compare two doubles: 1 or 0.
  FCmp : Rel -> Opnd var F64 -> Opnd var F64 -> Instr d m var [W64]
  Convert : (op : ConvOp) -> Opnd var (convFrom op) -> Instr d m var [convTo op]
  ||| Compare two integers: 1 or 0.
  Cmp : {auto 0 int : IsInt t} -> Rel -> Opnd var t -> Opnd var t -> Instr d m var [W64]
  Load : (t : Ty enc) -> Mem var -> Instr d m var [t]
  Store : (t : Ty enc) -> Mem var -> Opnd var t -> Instr d m var []
  ||| Load 8, 16 or 32 bits, extended to a word.
  LoadN : SubWord -> (signed : Bool) -> Mem var -> Instr d m var [W64]
  ||| Store a word's low 8, 16 or 32 bits.
  StoreN : SubWord -> Mem var -> Opnd var W64 -> Instr d m var []
  ||| The fixnum of a word the producer knows is in range.
  Tag : {auto 0 fx : HasFixnums enc.val} -> Opnd var W64 -> Instr d m var [Fix {enc}]
  Untag : {auto 0 fx : HasFixnums enc.val} -> Opnd var (Fix {enc}) -> Instr d m var [W64]
  ||| A `Val` the producer knows is a fixnum.
  NarrowFix : {auto 0 fx : HasFixnums enc.val} -> Opnd var Val -> Instr d m var [Fix {enc}]
  ||| A `Val` the producer knows points to an object of the kind.
  NarrowPtr : (k : Kind) -> Opnd var Val -> Instr d m var [PtrTo k]
  WidenFix : {auto 0 fx : HasFixnums enc.val} -> Opnd var (Fix {enc}) -> Instr d m var [Val]
  WidenPtr : Opnd var (PtrTo k) -> Instr d m var [Val]
  AddrToWord : Opnd var (PtrTo k) -> Instr d True var [W64]
  WordToAddr : (k : Kind) -> Opnd var W64 -> Instr d True var [PtrTo k]
  ||| The header word of an object; a continuation's layout word.
  LoadHeader : Opnd var (PtrTo k) -> Instr d m var [W64]
  LoadPart : {k : Kind} -> HeaderPart k -> Opnd var (PtrTo k) -> Instr d m var [W64]
  ||| A whole object in one step, from a header known when the program is
  ||| compiled and its fields.
  AllocObj : {k : Kind} -> (h : Header enc k) -> {auto 0 ok : So (wellFormed h)} ->
             All (Opnd var) (fieldTys h) -> Instr d m var [PtrTo k]
  ||| A whole object of a size known at run time: the count is the part.
  AllocSized : {k : Kind} -> (p : HeaderPart k) -> {auto 0 sizes : Sizes p} -> (count : Opnd var W64) ->
               Fill var p -> Instr d m var [PtrTo k]
  ||| A machine call of a Direct function, binding its results.
  DirectCall : Var d.sigs (MkSig n (InDirect rs col) ps cv) -> All (Opnd var) ps -> Instr d m var rs
  ReadHp : Instr d m var [W64]
  WriteHp : Opnd var W64 -> Instr d m var []
  ReadHpLim : Instr d m var [W64]
  WriteHpLim : Opnd var W64 -> Instr d m var []
  ReadK : Instr d m var [PtrTo CONT]
  WriteK : Opnd var (PtrTo CONT) -> Instr d m var []
  ReadStackPointer : Instr d m var [W64]
  WriteStackPointer : Opnd var W64 -> Instr d m var []
  ||| A system call: a number and up to six arguments.
  SystemCall : Opnd var W64 -> (args : Vect a (Opnd var W64)) -> {auto 0 ok : LTE a 6} -> Instr d m var [W64]
  ||| The source location of what follows.
  Loc : FC -> Instr d m var []
  Comment : String -> Instr d m var []

------------------------------------------------------------------------------
-- Traversals

||| The operands, each replaced, effectfully.
public export
traverseAll : Applicative f => ({0 t : Ty enc} -> Opnd v t -> f (Opnd w t)) -> All (Opnd v) ts -> f (All (Opnd w) ts)
traverseAll g [] = pure []
traverseAll g (x :: xs) = [| g x :: traverseAll g xs |]

public export
traverseMem : Applicative f => ({0 t : Ty enc} -> Opnd v t -> f (Opnd w t)) -> Mem v -> f (Mem w)
traverseMem g (MkMem (AtWord b) i o) = [| (\b', i' => MkMem (AtWord b') i' o) (g b) (traverse g i) |]
traverseMem g (MkMem (AtPtr b) i o) = [| (\b', i' => MkMem (AtPtr b') i' o) (g b) (traverse g i) |]

||| The instruction with each operand replaced, effectfully: how a pass
||| changes the representation of variables.
public export
traverseInstr : Applicative f => ({0 t : Ty enc} -> Opnd v t -> f (Opnd w t)) -> Instr d m v ts -> f (Instr d m w ts)
traverseInstr g (FConst x) = pure (FConst x)
traverseInstr g (CodeAddr r) = pure (CodeAddr r)
traverseInstr g (StaticAddr r) = pure (StaticAddr r)
traverseInstr g (AreaAddr a) = pure (AreaAddr a)
traverseInstr g (Arith {int} o x y) = [| (\x', y' => Arith {int} o x' y') (g x) (g y) |]
traverseInstr g (Unary o x) = Unary o <$> g x
traverseInstr g (Ext w s x) = Ext w s <$> g x
traverseInstr g (FArith o x y) = [| FArith (pure o) (g x) (g y) |]
traverseInstr g (FNeg x) = FNeg <$> g x
traverseInstr g (FCmp r x y) = [| FCmp (pure r) (g x) (g y) |]
traverseInstr g (Convert op x) = Convert op <$> g x
traverseInstr g (Cmp {int} r x y) = [| (\x', y' => Cmp {int} r x' y') (g x) (g y) |]
traverseInstr g (Load t mem) = Load t <$> traverseMem g mem
traverseInstr g (Store t mem x) = [| (\mem', x' => Store t mem' x') (traverseMem g mem) (g x) |]
traverseInstr g (LoadN w s mem) = LoadN w s <$> traverseMem g mem
traverseInstr g (StoreN w mem x) = [| StoreN (pure w) (traverseMem g mem) (g x) |]
traverseInstr g (Tag {fx} x) = Tag {fx} <$> g x
traverseInstr g (Untag {fx} x) = Untag {fx} <$> g x
traverseInstr g (NarrowFix {fx} x) = NarrowFix {fx} <$> g x
traverseInstr g (NarrowPtr k x) = NarrowPtr k <$> g x
traverseInstr g (WidenFix {fx} x) = WidenFix {fx} <$> g x
traverseInstr g (WidenPtr x) = WidenPtr <$> g x
traverseInstr g (AddrToWord x) = AddrToWord <$> g x
traverseInstr g (WordToAddr k x) = WordToAddr k <$> g x
traverseInstr g (LoadHeader x) = LoadHeader <$> g x
traverseInstr g (LoadPart p x) = LoadPart p <$> g x
traverseInstr g (AllocObj h {ok} fs) = (\fs' => AllocObj h {ok} fs') <$> traverseAll g fs
traverseInstr g (AllocSized ArrayElems {sizes} c f) = [| (\c', f' => AllocSized ArrayElems {sizes} c' f') (g c) (g f) |]
traverseInstr g (AllocSized StringBytes {sizes} c f) = (\c' => AllocSized StringBytes {sizes} c' f) <$> g c
traverseInstr g (AllocSized BufferBytes {sizes} c f) = (\c' => AllocSized BufferBytes {sizes} c' f) <$> g c
traverseInstr g (AllocSized ConId {sizes} c f) = (\c' => AllocSized ConId {sizes} c' f) <$> g c
traverseInstr g (AllocSized ConArity {sizes} c f) = (\c' => AllocSized ConArity {sizes} c' f) <$> g c
traverseInstr g (AllocSized ClosureArity {sizes} c f) = (\c' => AllocSized ClosureArity {sizes} c' f) <$> g c
traverseInstr g (AllocSized ClosureFilled {sizes} c f) = (\c' => AllocSized ClosureFilled {sizes} c' f) <$> g c
traverseInstr g (AllocSized BignumNegative {sizes} c f) = (\c' => AllocSized BignumNegative {sizes} c' f) <$> g c
traverseInstr g (AllocSized BignumWords {sizes} c f) = (\c' => AllocSized BignumWords {sizes} c' f) <$> g c
traverseInstr g (DirectCall r xs) = DirectCall r <$> traverseAll g xs
traverseInstr g ReadHp = pure ReadHp
traverseInstr g (WriteHp x) = WriteHp <$> g x
traverseInstr g ReadHpLim = pure ReadHpLim
traverseInstr g (WriteHpLim x) = WriteHpLim <$> g x
traverseInstr g ReadK = pure ReadK
traverseInstr g (WriteK x) = WriteK <$> g x
traverseInstr g ReadStackPointer = pure ReadStackPointer
traverseInstr g (WriteStackPointer x) = WriteStackPointer <$> g x
traverseInstr g (SystemCall {ok} n xs) = [| (\n', xs' => SystemCall {ok} n' xs') (g n) (traverse g xs) |]
traverseInstr g (Loc fc) = pure (Loc fc)
traverseInstr g (Comment s) = pure (Comment s)

------------------------------------------------------------------------------
-- Bodies

public export
Op : List (Ty enc) -> Ty enc -> Type
Op ctx = Opnd (Var ctx)

||| A body of a function of convention `c` that may (`m`) convert between
||| words and addresses, with the blocks `ls` (each its parameters' types)
||| and the variables `ctx` in scope.
public export
data Body : Decls enc -> Conv enc -> Bool -> List (List (Ty enc)) -> List (Ty enc) -> Type where
  Bind : {ts : List (Ty enc)} -> Instr d m (Var ctx) ts -> Body d c m ls (ts ++ ctx) -> Body d c m ls ctx
  ||| A join point: `block`, with parameters `ps`, which may jump to itself
  ||| (a loop); then `rest`, from which it is reached.
  Join : (ps : List (Ty enc)) -> (block : Body d c m (ps :: ls) (ps ++ ctx)) ->
         (rest : Body d c m (ps :: ls) ctx) -> Body d c m ls ctx
  Jump : Var ls ps -> All (Op ctx) ps -> Body d c m ls ctx
  ||| Compare two integers and branch.
  Branch : {auto 0 int : IsInt t} -> Rel -> Op ctx t -> Op ctx t -> (yes, no : Body d c m ls ctx) -> Body d c m ls ctx
  ||| Whether every one of the values, at least one, is a fixnum; the yes
  ||| branch has them as `Fix`es.
  IfFixnums : {auto 0 fx : HasFixnums enc.val} ->
              {n : Nat} -> Vect (S n) (Op ctx Val) ->
              (yes : Body d c m ls (replicate (S n) (Fix {enc}) ++ ctx)) ->
              (no : Body d c m ls ctx) -> Body d c m ls ctx
  ||| Integer arithmetic, or the overflow branch when the result does not
  ||| fit: 64 signed bits for `W64`s, the fixnum range for `Fix`es.
  ArithOv : {t : Ty enc} -> {auto 0 int : IsInt t} -> OvOp -> Op ctx t -> Op ctx t -> (ok : Body d c m ls (t :: ctx)) ->
            (overflow : Body d c m ls ctx) -> Body d c m ls ctx
  ||| The fixnum of a word, or the overflow branch when it is out of range.
  TagOv : {auto 0 fx : HasFixnums enc.val} ->
          Op ctx W64 -> (ok : Body d c m ls (Fix {enc} :: ctx)) -> (overflow : Body d c m ls ctx) -> Body d c m ls ctx
  ||| A branch on an integer to the case of its key, else to the default.
  Switch : {auto 0 int : IsInt t} -> Op ctx t -> (keys : List Int64) ->
           {auto 0 ok : So (distinct keys && keysFit t keys)} ->
           All (\_ => Body d c m ls ctx) keys -> (dflt : Body d c m ls ctx) -> Body d c m ls ctx
  Call : Var d.sigs (MkSig n InCPS ps cv) -> All (Op ctx) ps -> (resume : Body d InCPS m ls (Val :: ctx)) ->
         Body d InCPS m ls ctx
  TailCall : Var d.sigs (MkSig n InCPS ps cv) -> All (Op ctx) ps -> Body d InCPS m ls ctx
  ||| Apply a closure to one argument, through the runtime's apply routine.
  Apply : (fn, arg : Op ctx Val) -> (resume : Body d InCPS m ls (Val :: ctx)) -> Body d InCPS m ls ctx
  TailApply : (fn, arg : Op ctx Val) -> Body d InCPS m ls ctx
  Return : Op ctx Val -> Body d InCPS m ls ctx
  ||| Jump to a code address with arguments, under the current continuation:
  ||| the runtime's one way into Idris code.
  Enter : Op ctx W64 -> List (Op ctx Val) -> Body d c m ls ctx
  Ret : All (Op ctx) rs -> Body d (InDirect rs col) m ls ctx
  Crash : String -> Body d c m ls ctx
  ||| Exit with the abort status: a construct the backend does not lower yet.
  Unsupported : String -> Body d c m ls ctx

------------------------------------------------------------------------------
-- Programs

||| A word of a static object.
public export
data SField : Decls enc -> Type where
  SWord : Int64 -> SField d
  SRef : Var d.statics s -> SField d
  SCode : Var d.sigs (MkSig n InCPS ps cv) -> SField d

||| A function's definition: a body over its parameters, or a Direct routine
||| of the runtime, outside the program.
public export
data Def : Decls enc -> Sig enc -> Type where
  Defined : Body d s.conv s.converts [] s.params -> Def d s
  External : Def d (MkSig n (InDirect rs col) ps False)

||| A static object's definition: its header and its words after it.
public export
data StaticDef : Decls enc -> StaticSig -> Type where
  MkStaticDef : {0 d : Decls enc} -> {k : Kind} -> (h : Header enc k) -> {auto 0 ok : So (wellFormed h)} ->
                Vect (fieldWords h) (SField d) -> StaticDef d (MkStaticSig s k)

||| The entry: a CPS function of the program, of no parameters.
public export
data Entry : Decls enc -> Type where
  MkEntry : Var d.sigs (MkSig n InCPS [] cv) -> Entry d

||| A program: a definition for every function and static, under distinct
||| names, its entry, and the link-time numbering of its constructors.
public export
data Program : (enc : Enc) -> Decls enc -> Type where
  MkProgram : {auto 0 names : So (distinct (map (.name) d.sigs) && distinct (map (.sym) d.statics))} ->
              All (Def d) d.sigs -> All (StaticDef d) d.statics -> Entry d -> ConIds -> Program enc d
