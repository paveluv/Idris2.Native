||| What each function's code may leave changed in the registers, gathered
||| from its instructions as the rendering makes them (`Clobbers`), and the
||| check that a hand-written routine's declared clobbers cover what it and
||| the functions it calls write (`conforms`).
|||
||| A function's own writes are its instructions' (`Writes.writes`) but the
||| stack pointer's: a function and every call it makes give back the stack
||| they take, so the stack pointer is as it was when the function returns.
||| What a call may leave changed is the union of the own writes of every
||| function it reaches through calls, the callee's included: a function's
||| own writes do not depend on its callees', so no fixed point is needed.
module Native.Codegen.X86.Clobbers

import Native.Codegen.X86.Asm
import Native.Codegen.X86.RegSet
import Native.Codegen.X86.Writes

import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String

%default total

||| The functions' own writes and the labels they call, by each label a
||| function is entered at.
export
record Clobbers where
  constructor MkClobbers
  functions : SortedMap Asm.Label (RegSet, List Asm.Label)

||| No function recorded.
export
none : Clobbers
none = MkClobbers empty

||| The label a call calls.
callee : Asm.Instr -> Maybe Asm.Label
callee (Asm.Call l) = Just l
callee _ = Nothing

||| The function's code, its instructions as rendered, recorded under its
||| entry labels, those before its first instruction: its own writes and
||| the labels it calls.
export
add : List Asm.Instr -> Clobbers -> Clobbers
add is c =
  let own = RegSet.minus (foldl (\s, i => RegSet.union s (Writes.writes i)) RegSet.none is)
                         (RegSet.gpr Asm.RSP)
      entry = (own, mapMaybe callee is)
  in MkClobbers (foldl (\m, l => insert l entry m) c.functions (entries is))
  where
    entries : List Asm.Instr -> List Asm.Label
    entries (Asm.Comment _ :: rest) = entries rest
    entries (Asm.Lbl l :: rest) = l :: entries rest
    entries _ = []

||| The registers a routine restores: each it stores, in the run of stores
||| to fixed words of memory its code begins with (past its alignment and
||| labels), to a word it loads it back from, in the run of loads its code
||| ends with before its return. Whatever writes such a register in
||| between, the routine leaves it as it found it, but for what it writes
||| to the word on purpose.
export
restored : List Asm.Instr -> RegSet
restored is =
  let saved = stores (dropWhile prelude is)
      loaded = loads (reverse is)
  in foldl (\s, (r, l, o) => if elem (r, l, o) loaded then RegSet.union s (RegSet.gpr r) else s)
       RegSet.none saved
  where
    prelude : Asm.Instr -> Bool
    prelude (Asm.Align _) = True
    prelude (Asm.Lbl _) = True
    prelude _ = False

    stores : List Asm.Instr -> List (Asm.Reg64, Asm.Label, Int)
    stores (Asm.MovMR (Asm.MRip l o) r :: rest) = (r, l, o) :: stores rest
    stores _ = []

    -- the loads before the return, the last first
    loads : List Asm.Instr -> List (Asm.Reg64, Asm.Label, Int)
    loads (Asm.Ret :: rest) = go rest
      where
        go : List Asm.Instr -> List (Asm.Reg64, Asm.Label, Int)
        go (Asm.MovRM r (Asm.MRip l o) :: more) = (r, l, o) :: go more
        go _ = []
    loads _ = []

||| Whether the routine's code, which may call recorded functions, leaves
||| changed only registers `declared` names: else why not, the registers it
||| does not declare or the label it calls that no function was recorded at.
export
conforms : Clobbers -> (name : String) -> (declared : RegSet) -> List Asm.Instr -> Either String ()
conforms c name declared is = case reaching c is of
  Left l => Left (name ++ " calls label " ++ show l ++ ", which no function was recorded at")
  Right w =>
    let extra = RegSet.minus w declared
    in if null (RegSet.names extra) then Right ()
       else Left (name ++ " may change registers its contract does not name: "
                  ++ unwords (RegSet.names extra))
  where
    ||| What the code's own instructions write, and what the functions they call
    ||| reach, but the stack pointer: the registers a call of the code may leave
    ||| changed, or the first label called that no function was recorded at.
    reaching : Clobbers -> List Asm.Instr -> Either Asm.Label RegSet
    reaching c is =
      let own = foldl (\s, i => RegSet.union s (Writes.writes i)) RegSet.none is
      in map (\r => RegSet.minus (RegSet.union own r) (RegSet.gpr Asm.RSP))
           (go (fuel c) empty (mapMaybe callee is) RegSet.none)
      where
        fuel : Clobbers -> Nat
        fuel c' = S (length (SortedMap.toList c'.functions))

        -- the labels still to visit, with fuel for each function once
        go : Nat -> SortedSet Asm.Label -> List Asm.Label -> RegSet -> Either Asm.Label RegSet
        go _ _ [] acc = Right acc
        go Z _ (l :: _) _ = Left l
        go (S n) seen (l :: ls) acc =
          if contains l seen then go (S n) seen ls acc
          else case lookup l c.functions of
            Nothing => Left l
            Just (own, calls) => go n (insert l seen) (calls ++ ls) (RegSet.union acc own)
