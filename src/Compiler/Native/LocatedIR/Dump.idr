||| A text rendering of located-IR programs, for dumps and tests: one line per
||| instruction, `dst := Op operands`, with each block under its label and
||| its parameters.
module Compiler.Native.LocatedIR.Dump

import Data.Builder
import Compiler.Native.LocatedIR
import Core.Name
import Data.List
import Data.String

%default covering

regs : List (Reg enc) -> String
regs rs = "[" ++ joinBy ", " (map show rs) ++ "]"

ops : List (Operand enc) -> String
ops xs = joinBy ", " (map show xs)

-- The registers an instruction defines, before its `:=`.
results : List (Reg enc) -> String
results [] = ""
results ds = joinBy ", " (map show ds) ++ " := "

-- `w`: the access's width, the unit of the index.
mem : Nat -> MemRef enc -> String
mem w m = "[" ++ show m.base ++ maybe "" (\i => " + " ++ show i ++ "*" ++ show w) m.index
            ++ " + " ++ show m.offset ++ "]"

rel : Rel -> String
rel EqR = "=="
rel NeR = "!="
rel LtS = "<s"
rel LeS = "<=s"
rel GtS = ">s"
rel GeS = ">=s"
rel LtU = "<u"
rel LeU = "<=u"
rel GtU = ">u"
rel GeU = ">=u"

instr : Instr enc -> String
instr (Const d c) = show d ++ " := Const " ++ show c
instr (FConst d c) = show d ++ " := FConst " ++ show c
instr (CodeAddr d f) = show d ++ " := CodeAddr " ++ show f
instr (StaticAddr d s) = show d ++ " := StaticAddr " ++ show s
instr (AreaAddr d _) = show d ++ " := AreaAddr"
instr (Arith o d x y) = show d ++ " := " ++ show o ++ " " ++ ops [x, y]
instr i@(Unary _ d x) = show d ++ " := " ++ instrName i ++ " " ++ show x
instr (ArithOv o d x y l) = show d ++ " := " ++ show o ++ "Ov " ++ ops [x, y] ++ " overflow " ++ show l
instr (Ext _ s d x) = show d ++ " := Ext" ++ (if s then "S " else "Z ") ++ show x
instr i@(FArith _ d x y) = show d ++ " := " ++ instrName i ++ " " ++ show x ++ ", " ++ show y
instr (FNeg d x) = show d ++ " := FNeg " ++ show x
instr (FCmp r d x y) = show d ++ " := FCmp " ++ show x ++ " " ++ rel r ++ " " ++ show y
instr (Convert _ d x) = show d ++ " := Convert " ++ show x
instr (Cmp r d x y) = show d ++ " := Cmp " ++ show x ++ " " ++ rel r ++ " " ++ show y
instr (Load t d m) = show d ++ " := Load " ++ show t ++ " " ++ mem 8 m
instr (Store t m x) = "Store " ++ show t ++ " " ++ mem 8 m ++ " := " ++ show x
instr (LoadN sw _ d m) = show d ++ " := LoadN " ++ mem (subWordBytes sw) m
instr (StoreN sw m x) = "StoreN " ++ mem (subWordBytes sw) m ++ " := " ++ show x
instr (Tag d x) = show d ++ " := Tag " ++ show x
instr (Untag d x) = show d ++ " := Untag " ++ show x
instr (TagOv d x l) = show d ++ " := TagOv " ++ show x ++ " overflow " ++ show l
instr (Narrow t d x) = show d ++ " := Narrow " ++ show t ++ " " ++ show x
instr (Widen d x) = show d ++ " := Widen " ++ show x
instr (AddrToWord d x) = show d ++ " := AddrToWord " ++ show x
instr (WordToAddr k d x) = show d ++ " := WordToAddr " ++ show k ++ " " ++ show x
instr (LoadHeader d x) = show d ++ " := LoadHeader " ++ show x
instr (LoadPart p d x) = show d ++ " := LoadPart " ++ show p ++ " " ++ show x
instr (AllocObj d h fs live) = show d ++ " := AllocObj " ++ show h ++ " (" ++ ops fs ++ ") live " ++ regs live
instr (AllocSized d p n f live)
    = show d ++ " := AllocSized " ++ show p ++ "=" ++ show n
        ++ maybe "" (\o => " fill " ++ show o) f ++ " live " ++ regs live
instr (DirectCall f xs ds m live) =
  results ds ++ "DirectCall " ++ show f ++ " (" ++ ops xs ++ ")"
  ++ (if m then " mayCollect" else "") ++ " live " ++ regs live
instr i@(Intrinsic _ d xs) = maybe "" (\r => show r ++ " := ") d ++ instrName i ++ " (" ++ ops xs ++ ")"
instr (Move d s) = show d ++ " := " ++ show s
instr (Loc _) = "Loc"
instr (Comment s) = "-- " ++ s

cont : Cont enc -> String
cont c = "resume " ++ show c.resume ++ " live " ++ regs c.live

term : BlockTerminator enc -> String
term (Jump l) = "Jump " ++ show l
term (IsFixnum rs y n) = "IsFixnum " ++ regs rs ++ " " ++ show y ++ " " ++ show n
term (Branch r x y t f) = "Branch " ++ show x ++ " " ++ rel r ++ " " ++ show y ++ " " ++ show t ++ " " ++ show f
term (Switch r cs d) =
  "Switch " ++ show r ++ " [" ++ joinBy ", " (map (\c => show (fst c) ++ " -> " ++ show (snd c)) cs) ++ "] else " ++ show d
term (Call f xs c) = "Call " ++ show f ++ " (" ++ ops xs ++ ") " ++ cont c
term (TailCall f xs) = "TailCall " ++ show f ++ " (" ++ ops xs ++ ")"
term (Apply f x c) = "Apply " ++ show f ++ " " ++ show x ++ " " ++ cont c
term (TailApply f x) = "TailApply " ++ show f ++ " " ++ show x
term (Return v) = "Return " ++ show v
term (Enter c xs) = "Enter " ++ show c ++ " (" ++ ops xs ++ ")"
term (Ret vs) = "Ret" ++ (if null vs then "" else " " ++ ops vs)
term (Crash s) = "Crash " ++ show s
term (Unsupported s) = "Unsupported " ++ show s

-- A block's text, a line a piece.
blockPieces : Block enc -> Builder String
blockPieces b =
  single ("  " ++ show b.label ++ (if null b.params then "" else " " ++ regs b.params) ++ ":\n")
  <+> concatMap (\i => single ("    " ++ instr i ++ "\n")) b.body
  <+> single ("    " ++ term b.term ++ "\n")

functionPieces : Function enc -> Builder String
functionPieces f =
  single ("function " ++ show f.name ++ " " ++ show f.conv ++ " " ++ regs f.params
          ++ (if null f.results then "" else " -> " ++ show f.results)
          ++ " entry " ++ show f.entry ++ "\n")
  <+> concatMap blockPieces f.blocks

||| One function: its name, convention, parameters and blocks.
export
dumpFunction : Function enc -> String
dumpFunction f = fastConcat (contents (functionPieces f))

||| A whole program: the statics, then every function.
export
dumpProgram : Program enc -> String
dumpProgram p =
  fastConcat (contents (concatMap (\s => single ("static " ++ show s.sym ++ " " ++ show s.header ++ "\n")) p.statics
                        <+> concatMap (\f => functionPieces f <+> single "\n") p.functions))
