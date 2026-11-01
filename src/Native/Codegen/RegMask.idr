||| Sets of a target's allocatable registers (`RegMask`), a word a register
||| class: bit i of `words` stands for the word register at index i of the
||| target's description (`Native.Codegen.RegDesc`), bit i of `floats` for
||| the floating-point register at i. A description has fewer than 64
||| registers a class (`Native.Codegen.Target.wellFormed`), so every index
||| has its bit.
module Native.Codegen.RegMask

import Native.Codegen.RegDesc

import Data.Bits
import Native.Rep

%default total

public export
record RegMask where
  constructor MkRegMask
  words : Bits64
  floats : Bits64

||| No register.
export
none : RegMask
none = MkRegMask 0 0

||| Every register of the description.
export
every : RegDesc -> RegMask
every d = MkRegMask (below d.wordCount) (below d.floatCount)
  where
    below : Nat -> Bits64
    below n = prim__shl_Bits64 1 (cast n) - 1

||| The register of the class at the index, alone.
export
single : Rep.RegClass -> Nat -> RegMask
single Rep.WordClass i = MkRegMask (prim__shl_Bits64 1 (cast i)) 0
single Rep.FloatClass i = MkRegMask 0 (prim__shl_Bits64 1 (cast i))

||| The registers of either set.
export
union : RegMask -> RegMask -> RegMask
union a b = MkRegMask (a.words .|. b.words) (a.floats .|. b.floats)

||| Whether the register of the class at the index is in the set.
export
member : Rep.RegClass -> Nat -> RegMask -> Bool
member c i s =
  let b = single c i in ((s.words .&. b.words) .|. (s.floats .&. b.floats)) /= 0
