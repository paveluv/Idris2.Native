||| The registers a target gives register allocation (`RegDesc`): of each
||| register class, the registers values may be kept in, in the order the
||| allocator prefers them, by the target's own numbering (`TargetReg`,
||| `FloatReg` in `Native.Codegen.Target`).
|||
||| A location of the located IR names a register by its index here, never
||| by its number, so a register the target keeps for itself (the pinned
||| ones, the stack pointer, the slots' base) has no index and cannot be
||| named. A target's description is checked where it is defined
||| (`Native.Codegen.Target.wellFormed`).
module Native.Codegen.RegDesc

%default total

public export
record RegDesc where
  constructor MkRegDesc
  ||| The word registers, by the target's numbers.
  words : List Nat
  ||| The floating-point registers, by the target's numbers.
  floats : List Nat
  ||| How many of each there are, kept so that a location's number is read
  ||| without counting them.
  wordCount : Nat
  floatCount : Nat

||| The description of the registers, counted.
public export
regDesc : (words, floats : List Nat) -> RegDesc
regDesc ws fs = MkRegDesc ws fs (length ws) (length fs)
