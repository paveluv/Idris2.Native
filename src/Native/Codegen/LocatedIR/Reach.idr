||| A program cut to what it reaches (`reach`): the functions and statics
||| that its entry and its roots refer to, directly or through others; the
||| rest is left out of the image.
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

||| What a program refers to by name: functions (`code`) and statics.
record Refs where
  constructor MkRefs
  code : List Name
  statics : List Name

Semigroup Refs where
  MkRefs a b <+> MkRefs a' b' = MkRefs (a ++ a') (b ++ b')

Monoid Refs where
  neutral = MkRefs [] []

||| The program with only the functions and statics its entry and the
||| functions of `roots` reach, in their order. A name that is no function
||| or static of the program is left for the rendering to report.
export
reach : (roots : Name -> Bool) -> Program enc -> Program enc
reach roots p =
  let funs = fromList (map (\f => (f.name, f)) p.functions)
      stats = fromList (map (\s => (s.sym, s)) p.statics)
      start = p.entry :: [ f.name | f <- p.functions, roots f.name ]
      (cs, ss) =
        go funs stats (MkRefs start []) empty empty (length p.functions + length p.statics)
  in { functions := filter (\f => contains f.name cs) p.functions
     , statics := filter (\s => contains s.sym ss) p.statics } p
  where
    ||| The names a function refers to.
    function : Function enc -> Refs
    function f = concatMap (\b => concatMap instr b.body <+> terminator b.term) f.blocks
      where
        ||| The names an operand refers to: a static's.
        opnd : Opnd enc' -> Refs
        opnd (Opnd.StaticRef n) = MkRefs [] [n]
        opnd _ = neutral

        opnds : List (Opnd enc') -> Refs
        opnds = concatMap opnd

        ||| The names an instruction refers to.
        instr : Instr enc -> Refs
        instr (Instr.CodeOf _ f) = MkRefs [f] []
        instr (Instr.StaticAddr _ s) = MkRefs [] [s]
        instr (Instr.Arith _ _ x y) = opnds [x, y]
        instr (Instr.Mul128 _ _ x y) = opnds [x, y]
        instr (Instr.Div128 _ _ h l x) = opnds [h, l, x]
        instr (Instr.ArithOv _ _ x y _) = opnds [x, y]
        instr (Instr.Cmp _ _ x y) = opnds [x, y]
        instr (Instr.AllocObj _ _ fields _) = opnds fields
        instr (Instr.AllocSized _ _ _ fill _) = maybe neutral opnd fill
        instr (Instr.DirectCall f xs _ _ _) = MkRefs [f] [] <+> opnds xs
        instr (Instr.SetPinned _ x) = opnd x
        instr (Instr.SystemCall _ xs) = opnds xs
        instr _ = neutral

        ||| The names a terminator refers to.
        terminator : Terminator enc -> Refs
        terminator (Terminator.Branch _ x y _ _) = opnds [x, y]
        terminator (Terminator.Call f xs _) = MkRefs [f] [] <+> opnds xs
        terminator (Terminator.TailCall f xs) = MkRefs [f] [] <+> opnds xs
        terminator (Terminator.Return x) = opnd x
        terminator (Terminator.Enter _ xs) = opnds xs
        terminator (Terminator.Ret xs) = opnds xs
        terminator _ = neutral

    ||| The names a static refers to: the code and the statics its fields hold.
    static : Static enc -> Refs
    static s = concatMap field s.fields
      where
        field : Static.SField -> Refs
        field (Static.SCode f) = MkRefs [f] []
        field (Static.SRef t) = MkRefs [] [t]
        field _ = neutral

    -- the names still to follow, and those reached; each name is followed
    -- once, so the fuel, every function and static once, is enough
    go : SortedMap Name (Function enc) -> SortedMap Name (Static enc) -> Refs ->
         (code, statics : SortedSet Name) -> (fuel : Nat) -> (SortedSet Name, SortedSet Name)
    go funs stats (MkRefs [] []) cs ss _ = (cs, ss)
    go funs stats _ cs ss Z = (cs, ss)
    go funs stats (MkRefs (f :: fs) ss') cs ss (S k) =
      if contains f cs then go funs stats (MkRefs fs ss') cs ss (S k) else
        let more = maybe neutral function (lookup f funs)
        in go funs stats (MkRefs fs ss' <+> more) (insert f cs) ss k
    go funs stats (MkRefs [] (s :: ss')) cs ss (S k) =
      if contains s ss then go funs stats (MkRefs [] ss') cs ss (S k) else
        let more = maybe neutral static (lookup s stats)
        in go funs stats (MkRefs [] ss' <+> more) cs (insert s ss) k
