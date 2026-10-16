||| A whole program in the term IR (`Program`).
|||
||| The term IR, the modules of `Native.Codegen.TermIR`: the native backend's
||| IR as a typed, scoped term.
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
||| The term is the input of `Native.Codegen.RegAlloc`, which turns it into
||| the IR, computing every live list. Producers build it through
||| `Native.Codegen.TermIR.Build`.
module Native.Codegen.TermIR.Program

import Native.Codegen.TermIR.Decls
import Native.Codegen.TermIR.Def
import Native.Codegen.TermIR.Sig
import Native.Codegen.TermIR.StaticDef
import Native.Codegen.TermIR.StaticSig
import Native.Codegen.TermIR.Var

import Core.Name
import Data.List.Quantifiers
import Data.So
import Native.Codegen.IRCommon.ConIds as IRCommon
import Native.Codegen.IRCommon.Conv
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Data.Distinct
import Native.HeapObj.Enc as HeapObj

%default total

||| The entry: a CPS function of the program, of no parameters.
public export
data Entry : Decls enc -> Type where
  MkEntry : Var d.sigs (MkSig n IRCommon.Conv.CPS [] cv) -> Entry d

||| A program: a definition for every function and static, under distinct
||| names, its entry, and the link-time numbering of its constructors.
public export
data Program : (enc : HeapObj.Enc) -> Decls enc -> Type where
  MkProgram : {auto 0 names : So (distinct (map (.name) d.sigs) && distinct (map (.sym) d.statics))} ->
              All (Def d) d.sigs -> All (StaticDef d) d.statics -> Entry d -> IRCommon.ConIds -> Program enc d

||| A program with its declarations, as a producer hands it on.
public export
TermProgram : HeapObj.Enc -> Type
TermProgram enc = (d : Decls enc ** Program enc d)
