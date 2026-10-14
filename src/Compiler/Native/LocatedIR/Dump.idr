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

import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.Header as HeapObject
import Compiler.Native.HeapObject.Kind as HeapObject
import Compiler.Native.IRCommon.Conv as IRCommon
import Compiler.Native.IRCommon.Operators
import Compiler.Native.IRCommon.Ty as IRCommon
import Core.Name
import Data.Builder as Data
import Data.String

%default covering

functionPieces : Function enc -> Data.Builder String
functionPieces f =
  Data.Builder.single ("function " ++ show f.name ++ " " ++ show f.conv ++ " " ++ regs f.params
          ++ (if null (IRCommon.Conv.results f.conv) then "" else " -> " ++ show (IRCommon.Conv.results f.conv))
          ++ " entry " ++ show f.entry ++ "\n")
  <+> concatMap blockPieces f.blocks
  where
    regs : List (Reg enc') -> String
    regs rs = "[" ++ joinBy ", " (map show rs) ++ "]"

    -- A block's text, a line a piece.
    blockPieces : Block enc''' -> Data.Builder String
    blockPieces b =
      Data.Builder.single ("  " ++ show b.label ++ (if null b.params then "" else " " ++ regs b.params) ++ ":\n")
      <+> concatMap (\i => Data.Builder.single ("    " ++ instr i ++ "\n")) b.body
      <+> Data.Builder.single ("    " ++ term b.term ++ "\n")
      where
        ops : List (Opnd enc') -> String
        ops xs = joinBy ", " (map show xs)

        rel : IRCommon.Operators.Rel -> String
        rel IRCommon.Operators.EqR = "=="
        rel IRCommon.Operators.NeR = "!="
        rel IRCommon.Operators.LtS = "<s"
        rel IRCommon.Operators.LeS = "<=s"
        rel IRCommon.Operators.GtS = ">s"
        rel IRCommon.Operators.GeS = ">=s"
        rel IRCommon.Operators.LtU = "<u"
        rel IRCommon.Operators.LeU = "<=u"
        rel IRCommon.Operators.GtU = ">u"
        rel IRCommon.Operators.GeU = ">=u"

        instr : Instr enc'' -> String
        instr instr' = case instr' of
          Instr.Const d c => show d ++ " := Const " ++ show c
          Instr.FConst d c => show d ++ " := FConst " ++ show c
          Instr.CodeAddr d f => show d ++ " := CodeAddr " ++ show f
          Instr.StaticAddr d s => show d ++ " := StaticAddr " ++ show s
          Instr.AreaAddr d _ => show d ++ " := AreaAddr"
          Instr.Arith o d x y => show d ++ " := " ++ show o ++ " " ++ ops [x, y]
          i@(Instr.Unary _ d x) => show d ++ " := " ++ Instr.instrName i ++ " " ++ show x
          Instr.ArithOv o d x y l => show d ++ " := " ++ show o ++ "Ov " ++ ops [x, y] ++ " overflow " ++ show l
          Instr.Ext _ s d x => show d ++ " := Ext" ++ (if s then "S " else "Z ") ++ show x
          i@(Instr.FArith _ d x y) => show d ++ " := " ++ Instr.instrName i ++ " " ++ show x ++ ", " ++ show y
          Instr.FNeg d x => show d ++ " := FNeg " ++ show x
          Instr.FCmp r d x y => show d ++ " := FCmp " ++ show x ++ " " ++ rel r ++ " " ++ show y
          Instr.Convert _ d x => show d ++ " := Convert " ++ show x
          Instr.Cmp r d x y => show d ++ " := Cmp " ++ show x ++ " " ++ rel r ++ " " ++ show y
          Instr.Load t d m => show d ++ " := Load " ++ show t ++ " " ++ mem 8 m
          Instr.Store t m x => "Store " ++ show t ++ " " ++ mem 8 m ++ " := " ++ show x
          Instr.LoadN sw _ d m => show d ++ " := LoadN " ++ mem (IRCommon.Operators.subWordBytes sw) m
          Instr.StoreN sw m x => "StoreN " ++ mem (IRCommon.Operators.subWordBytes sw) m ++ " := " ++ show x
          Instr.Tag d x => show d ++ " := Tag " ++ show x
          Instr.Untag d x => show d ++ " := Untag " ++ show x
          Instr.TagOv d x l => show d ++ " := TagOv " ++ show x ++ " overflow " ++ show l
          Instr.Narrow t d x => show d ++ " := Narrow " ++ show t ++ " " ++ show x
          Instr.Widen d x => show d ++ " := Widen " ++ show x
          Instr.AddrToWord d x => show d ++ " := AddrToWord " ++ show x
          Instr.WordToAddr k d x => show d ++ " := WordToAddr " ++ show k ++ " " ++ show x
          Instr.LoadHeader d x => show d ++ " := LoadHeader " ++ show x
          Instr.LoadPart p d x => show d ++ " := LoadPart " ++ show p ++ " " ++ show x
          Instr.AllocObj d h fs live => show d ++ " := AllocObj " ++ show h ++ " (" ++ ops fs ++ ") live " ++ regs live
          Instr.AllocSized d p n f live
                   => show d ++ " := AllocSized " ++ show p ++ "=" ++ show n
                        ++ maybe "" (\o => " fill " ++ show o) f ++ " live " ++ regs live
          Instr.DirectCall f xs ds m live =>
                  assigned ds ++ "DirectCall " ++ show f ++ " (" ++ ops xs ++ ")"
                  ++ (if m then " mayCollect" else "") ++ " live " ++ regs live
          i@(Instr.Intrinsic _ ds xs) => assigned ds ++ Instr.instrName i ++ " (" ++ ops xs ++ ")"
          Instr.Move d s => show d ++ " := " ++ show s
          Instr.Loc _ => "Loc"
          Instr.Comment s => "-- " ++ s
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
          Terminator.Jump l => "Jump " ++ show l
          Terminator.IfFixnums rs y n => "IfFixnums " ++ regs rs ++ " " ++ show y ++ " " ++ show n
          Terminator.Branch r x y t f => "Branch " ++ show x ++ " " ++ rel r ++ " " ++ show y ++ " " ++ show t ++ " " ++ show f
          Terminator.Switch r cs d =>
                       "Switch " ++ show r ++ " [" ++ joinBy ", " (map (\c => show (fst c) ++ " -> " ++ show (snd c)) cs) ++ "] else " ++ show d
          Terminator.Call f xs c => "Call " ++ show f ++ " (" ++ ops xs ++ ") " ++ cont c
          Terminator.TailCall f xs => "TailCall " ++ show f ++ " (" ++ ops xs ++ ")"
          Terminator.Apply f x c => "Apply " ++ show f ++ " " ++ show x ++ " " ++ cont c
          Terminator.TailApply f x => "TailApply " ++ show f ++ " " ++ show x
          Terminator.Return v => "Return " ++ show v
          Terminator.Enter c xs => "Enter " ++ show c ++ " (" ++ ops xs ++ ")"
          Terminator.Ret vs => "Ret" ++ (if null vs then "" else " " ++ ops vs)
          Terminator.Crash s => "Crash " ++ show s
          Terminator.Unsupported s => "Unsupported " ++ show s
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
dumpProgram : Program enc -> Data.Builder String
dumpProgram p =
  concatMap (\s => Data.Builder.single ("static " ++ show s.sym ++ " " ++ show s.header ++ "\n")) p.statics
  <+> concatMap (\f => functionPieces f <+> Data.Builder.single "\n") p.functions
