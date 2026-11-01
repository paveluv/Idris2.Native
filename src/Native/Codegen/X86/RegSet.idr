||| Sets of x86-64 registers (`RegSet`), the general ones and the XMM ones,
||| as one word: bit n stands for the general register numbered n
||| (`Asm.regNum`), bit 16 + n for the XMM register numbered n
||| (`Asm.xmmNum`).
module Native.Codegen.X86.RegSet

import Native.Codegen.X86.Asm

import Data.Bits

%default total

public export
record RegSet where
  constructor MkRegSet
  bits : Bits32

||| No register.
export
none : RegSet
none = MkRegSet 0

||| The general register alone.
export
gpr : Asm.Reg64 -> RegSet
gpr r = MkRegSet (prim__shl_Bits32 1 (cast (Asm.regNum r)))

||| The XMM register alone.
export
xmm : Asm.Xmm -> RegSet
xmm x = MkRegSet (prim__shl_Bits32 1 (16 + cast (Asm.xmmNum x)))

||| The general registers given.
export
gprs : List Asm.Reg64 -> RegSet
gprs = foldr (\r, s => MkRegSet (s.bits .|. (gpr r).bits)) none

||| The registers of either set.
export
union : RegSet -> RegSet -> RegSet
union a b = MkRegSet (a.bits .|. b.bits)

||| The registers of both sets.
export
intersection : RegSet -> RegSet -> RegSet
intersection a b = MkRegSet (a.bits .&. b.bits)

||| Whether every register of the first set is in the second.
export
within : RegSet -> RegSet -> Bool
within a b = a.bits .&. complement b.bits == 0

||| Whether the general register is in the set.
export
hasGpr : Asm.Reg64 -> RegSet -> Bool
hasGpr r s = within (gpr r) s

||| Whether the XMM register is in the set.
export
hasXmm : Asm.Xmm -> RegSet -> Bool
hasXmm x s = within (xmm x) s

||| The registers of the first set that are not in the second.
export
minus : RegSet -> RegSet -> RegSet
minus a b = MkRegSet (a.bits .&. complement b.bits)

||| The set's registers' names, the general ones first, each in its order.
export
names : RegSet -> List String
names s =
  [ show r | r <- [ Asm.RAX, Asm.RCX, Asm.RDX, Asm.RBX, Asm.RSP, Asm.RBP, Asm.RSI, Asm.RDI
                  , Asm.R8, Asm.R9, Asm.R10, Asm.R11, Asm.R12, Asm.R13, Asm.R14, Asm.R15 ]
           , hasGpr r s ] ++
  [ show x | x <- [ Asm.XMM0, Asm.XMM1, Asm.XMM2, Asm.XMM3, Asm.XMM4, Asm.XMM5, Asm.XMM6
                  , Asm.XMM7, Asm.XMM8, Asm.XMM9, Asm.XMM10, Asm.XMM11, Asm.XMM12, Asm.XMM13
                  , Asm.XMM14, Asm.XMM15 ]
           , hasXmm x s ]
