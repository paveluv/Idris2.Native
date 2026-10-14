||| A text rendering of located-IR programs, for dumps and tests: one line per
||| instruction, `dst := Op operands`, with each block under its label and
||| its parameters.
module Compiler.Native.LocatedIR.Dump

import Compiler.Native.LocatedIR.Block
import Compiler.Native.LocatedIR.Cont
import Compiler.Native.LocatedIR.Function
import Compiler.Native.LocatedIR.Instr
import Compiler.Native.LocatedIR.Label
import Compiler.Native.LocatedIR.Mem
import Compiler.Native.LocatedIR.Opnd
import Compiler.Native.LocatedIR.Program
import Compiler.Native.LocatedIR.Reg
import Compiler.Native.LocatedIR.Static
import Compiler.Native.LocatedIR.Terminator

import Compiler.Native.HeapObject.Enc
import Compiler.Native.HeapObject.Header
import Compiler.Native.HeapObject.Kind
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Operators.ArithOp
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.IRCommon.Operators.SubWord
import Compiler.Native.IRCommon.Ty
import Core.Name
import Data.Builder
import Data.String

%default covering

functionPieces : Function enc -> Builder String
functionPieces f =
  single ("function " ++ show f.name ++ " " ++ show f.conv ++ " " ++ regs f.params
          ++ (if null (results f.conv) then "" else " -> " ++ show (results f.conv))
          ++ " entry " ++ show f.entry ++ "\n")
  <+> concatMap blockPieces f.blocks
  where
    regs : List (Reg enc') -> String
    regs rs = "[" ++ joinBy ", " (map show rs) ++ "]"

    -- A block's text, a line a piece.
    blockPieces : Block enc''' -> Builder String
    blockPieces b =
      single ("  " ++ show b.label ++ (if null b.params then "" else " " ++ regs b.params) ++ ":\n")
      <+> concatMap (\i => single ("    " ++ instr i ++ "\n")) b.body
      <+> single ("    " ++ term b.term ++ "\n")
      where
        ops : List (Opnd enc') -> String
        ops xs = joinBy ", " (map show xs)

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

        instr : Instr enc'' -> String
        instr instr' = case instr' of
          Const d c => show d ++ " := Const " ++ show c
          FConst d c => show d ++ " := FConst " ++ show c
          CodeAddr d f => show d ++ " := CodeAddr " ++ show f
          StaticAddr d s => show d ++ " := StaticAddr " ++ show s
          AreaAddr d _ => show d ++ " := AreaAddr"
          Arith o d x y => show d ++ " := " ++ show o ++ " " ++ ops [x, y]
          i@(Unary _ d x) => show d ++ " := " ++ instrName i ++ " " ++ show x
          ArithOv o d x y l => show d ++ " := " ++ show o ++ "Ov " ++ ops [x, y] ++ " overflow " ++ show l
          Ext _ s d x => show d ++ " := Ext" ++ (if s then "S " else "Z ") ++ show x
          i@(FArith _ d x y) => show d ++ " := " ++ instrName i ++ " " ++ show x ++ ", " ++ show y
          FNeg d x => show d ++ " := FNeg " ++ show x
          FCmp r d x y => show d ++ " := FCmp " ++ show x ++ " " ++ rel r ++ " " ++ show y
          Convert _ d x => show d ++ " := Convert " ++ show x
          Cmp r d x y => show d ++ " := Cmp " ++ show x ++ " " ++ rel r ++ " " ++ show y
          Load t d m => show d ++ " := Load " ++ show t ++ " " ++ mem 8 m
          Store t m x => "Store " ++ show t ++ " " ++ mem 8 m ++ " := " ++ show x
          LoadN sw _ d m => show d ++ " := LoadN " ++ mem (subWordBytes sw) m
          StoreN sw m x => "StoreN " ++ mem (subWordBytes sw) m ++ " := " ++ show x
          Tag d x => show d ++ " := Tag " ++ show x
          Untag d x => show d ++ " := Untag " ++ show x
          TagOv d x l => show d ++ " := TagOv " ++ show x ++ " overflow " ++ show l
          Narrow t d x => show d ++ " := Narrow " ++ show t ++ " " ++ show x
          Widen d x => show d ++ " := Widen " ++ show x
          AddrToWord d x => show d ++ " := AddrToWord " ++ show x
          WordToAddr k d x => show d ++ " := WordToAddr " ++ show k ++ " " ++ show x
          LoadHeader d x => show d ++ " := LoadHeader " ++ show x
          LoadPart p d x => show d ++ " := LoadPart " ++ show p ++ " " ++ show x
          AllocObj d h fs live => show d ++ " := AllocObj " ++ show h ++ " (" ++ ops fs ++ ") live " ++ regs live
          AllocSized d p n f live
             => show d ++ " := AllocSized " ++ show p ++ "=" ++ show n
                  ++ maybe "" (\o => " fill " ++ show o) f ++ " live " ++ regs live
          DirectCall f xs ds m live =>
            assigned ds ++ "DirectCall " ++ show f ++ " (" ++ ops xs ++ ")"
            ++ (if m then " mayCollect" else "") ++ " live " ++ regs live
          i@(Intrinsic _ ds xs) => assigned ds ++ instrName i ++ " (" ++ ops xs ++ ")"
          Move d s => show d ++ " := " ++ show s
          Loc _ => "Loc"
          Comment s => "-- " ++ s
          where
            -- The registers an instruction defines, before its `:=`.
            assigned : List (Reg enc') -> String
            assigned [] = ""
            assigned ds = joinBy ", " (map show ds) ++ " := "

            -- `w`: the access's width, the unit of the index.
            mem : Nat -> Mem enc' -> String
            mem w m = "[" ++ show m.base ++ maybe "" (\i => " + " ++ show i ++ "*" ++ show w) m.index
                        ++ " + " ++ show m.offset ++ "]"

        term : Terminator enc'' -> String
        term terminator = case terminator of
          Jump l => "Jump " ++ show l
          IfFixnums rs y n => "IfFixnums " ++ regs rs ++ " " ++ show y ++ " " ++ show n
          Branch r x y t f => "Branch " ++ show x ++ " " ++ rel r ++ " " ++ show y ++ " " ++ show t ++ " " ++ show f
          Switch r cs d =>
            "Switch " ++ show r ++ " [" ++ joinBy ", " (map (\c => show (fst c) ++ " -> " ++ show (snd c)) cs) ++ "] else " ++ show d
          Call f xs c => "Call " ++ show f ++ " (" ++ ops xs ++ ") " ++ cont c
          TailCall f xs => "TailCall " ++ show f ++ " (" ++ ops xs ++ ")"
          Apply f x c => "Apply " ++ show f ++ " " ++ show x ++ " " ++ cont c
          TailApply f x => "TailApply " ++ show f ++ " " ++ show x
          Return v => "Return " ++ show v
          Enter c xs => "Enter " ++ show c ++ " (" ++ ops xs ++ ")"
          Ret vs => "Ret" ++ (if null vs then "" else " " ++ ops vs)
          Crash s => "Crash " ++ show s
          Unsupported s => "Unsupported " ++ show s
          where
            cont : Cont enc' -> String
            cont c = "resume " ++ show c.resume ++ " live " ++ regs c.live

||| One function: its name, convention, parameters and blocks.
export
dumpFunction : Function enc -> String
dumpFunction f = fastConcat (toList (functionPieces f))

||| A whole program, in pieces to write a piece at a time: the statics, then
||| every function.
export
dumpProgram : Program enc -> Builder String
dumpProgram p =
  concatMap (\s => single ("static " ++ show s.sym ++ " " ++ show s.header ++ "\n")) p.statics
  <+> concatMap (\f => functionPieces f <+> single "\n") p.functions
