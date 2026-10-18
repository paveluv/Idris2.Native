||| A program cut to what it reaches (`reach`): the functions and statics
||| that its entry and its roots refer to, directly or through others, and
||| the tables they read; the rest is left out of the image.
module Native.Codegen.LocatedIR.Reach

import Native.Codegen.LocatedIR.Block
import Native.Codegen.LocatedIR.Function
import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Opnd
import Native.Codegen.LocatedIR.Program
import Native.Codegen.LocatedIR.Static
import Native.Codegen.LocatedIR.Terminator

import Core.Name
import Data.SortedMap
import Data.SortedSet
import Native.Types.Enc as Types

%default total

||| What a program refers to by name: functions (`code`), statics and tables.
record Refs where
  constructor MkRefs
  code : List Name
  statics : List Name
  tables : List Name

Semigroup Refs where
  MkRefs a b c <+> MkRefs a' b' c' = MkRefs (a ++ a') (b ++ b') (c ++ c')

Monoid Refs where
  neutral = MkRefs [] [] []

||| The names an operand refers to: a static's.
opnd : Opnd enc -> Refs
opnd (StaticRef n) = MkRefs [] [n] []
opnd _ = neutral

opnds : List (Opnd enc) -> Refs
opnds = concatMap opnd

||| The names an instruction refers to.
instr : Instr enc -> Refs
instr (CodeAddr _ f) = MkRefs [f] [] []
instr (StaticAddr _ s) = MkRefs [] [s] []
instr (TableAddr _ t) = MkRefs [] [] [t]
instr (Arith _ _ x y) = opnds [x, y]
instr (Mul128 _ _ x y) = opnds [x, y]
instr (ArithOv _ _ x y _) = opnds [x, y]
instr (Cmp _ _ x y) = opnds [x, y]
instr (AllocObj _ _ fields _) = opnds fields
instr (AllocSized _ _ _ fill _) = maybe neutral opnd fill
instr (DirectCall f xs _ _ _) = MkRefs [f] [] [] <+> opnds xs
instr (SetPinned _ x) = opnd x
instr (SystemCall _ xs) = opnds xs
instr _ = neutral

||| The names a terminator refers to.
terminator : Terminator enc -> Refs
terminator (Branch _ x y _ _) = opnds [x, y]
terminator (Call f xs _) = MkRefs [f] [] [] <+> opnds xs
terminator (TailCall f xs) = MkRefs [f] [] [] <+> opnds xs
terminator (Return x) = opnd x
terminator (Enter _ xs) = opnds xs
terminator (Ret xs) = opnds xs
terminator _ = neutral

||| The names a function refers to.
function : Function enc -> Refs
function f = concatMap (\b => concatMap instr b.body <+> terminator b.term) f.blocks

||| The names a static refers to: the code and the statics its fields hold.
static : Static enc -> Refs
static s = concatMap field s.fields
  where
    field : SField -> Refs
    field (SCode f) = MkRefs [f] [] []
    field (SRef t) = MkRefs [] [t] []
    field _ = neutral

||| The program with only the functions and statics its entry and the
||| functions of `roots` reach, in their order, and the tables they read. A
||| name that is no function or static of the program is left for the
||| rendering to report.
export
reach : (roots : Name -> Bool) -> Program enc -> (Program enc, List Name)
reach roots p =
  let funs = fromList (map (\f => (f.name, f)) p.functions)
      stats = fromList (map (\s => (s.sym, s)) p.statics)
      start = p.entry :: [ f.name | f <- p.functions, roots f.name ]
      (cs, ss, ts) = go funs stats (MkRefs start [] []) empty empty empty (length p.functions + length p.statics)
  in ({ functions := filter (\f => contains f.name cs) p.functions
      , statics := filter (\s => contains s.sym ss) p.statics } p, Data.SortedSet.toList ts)
  where
    -- the names still to follow, and those reached; each name is followed
    -- once, so the fuel, every function and static once, is enough
    go : SortedMap Name (Function enc) -> SortedMap Name (Static enc) -> Refs ->
         (code, statics, tables : SortedSet Name) -> (fuel : Nat) -> (SortedSet Name, SortedSet Name, SortedSet Name)
    go funs stats (MkRefs [] [] ts) cs ss tables _ = (cs, ss, foldr insert tables ts)
    go funs stats _ cs ss tables Z = (cs, ss, tables)
    go funs stats (MkRefs (f :: fs) ss' ts) cs ss tables (S k) =
      if contains f cs then go funs stats (MkRefs fs ss' ts) cs ss tables (S k) else
        let more = maybe neutral function (lookup f funs)
        in go funs stats (MkRefs fs ss' ts <+> more) (insert f cs) ss tables k
    go funs stats (MkRefs [] (s :: ss') ts) cs ss tables (S k) =
      if contains s ss then go funs stats (MkRefs [] ss' ts) cs ss tables (S k) else
        let more = maybe neutral static (lookup s stats)
        in go funs stats (MkRefs [] ss' ts <+> more) cs (insert s ss) tables k
