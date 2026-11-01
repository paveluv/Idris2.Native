-- A parallel move (`Par` in the located IR) made moves one at a time
-- (`Native.Codegen.Sequentialise.sequential`). A jump to a loop's head is
-- one: the Idris
--
--     go : Nat -> Int -> Int -> Int
--     go n x y = go (pred n) y x
--
-- passes y as x and x as y at once, x's old value read before x is
-- written. Moves one at a time must do the same, in some order, keeping
-- one value aside when the moves form a cycle, as a swap does.
--
-- Each case is a parallel move of slots (`slotN:T`), printed with the
-- moves it becomes. The register a cycle is broken through is the
-- target's, x86-64's rcx for words (word register 1, `reg1`), xmm1 for
-- doubles. Each is checked on a model: a store where every place starts
-- holding its own name, run through the moves one at a time, must hold,
-- at each destination, what its source held before, and everywhere else
-- but the register, what it held.
--
-- * x to itself: no move at all;
-- * a chain, one place to the next: no cycle, the move whose destination
--   nothing else reads first;
-- * a swap, as `go`'s: x kept in the register, y into x, then the register
--   into y;
-- * a cycle of three;
-- * a cycle with a branch, x read by two moves;
-- * two swaps, the register used for one, then again for the other;
-- * a swap of two doubles, through xmm1.
module Main

import Data.List
import Data.Maybe
import Native.Codegen.IRCommon.Ty
import Native.Codegen.LocatedIR.Instr
import Native.Codegen.LocatedIR.Location
import Native.Codegen.Sequentialise
import Native.Codegen.X86.Rows
import Native.HeapObj.ValEnc
import Native.Rep
import Native.Types.BignumEnc
import Native.Types.Enc
import Native.Types.StringEnc

%default total

TestEnc : Types.Enc.Enc
TestEnc = defaultEnc

word : Nat -> Location TestEnc
word n = Slot n W64

double : Nat -> Location TestEnc
double n = Slot n F64

||| A place's name in the model, which also tells the two classes'
||| registers apart.
place : Location TestEnc -> String
place l@(Register _ t) = show l
place (Slot n _) = "slot" ++ show n

||| A store of the model: what each place holds, its own name until a move
||| writes it.
Store : Type
Store = List (String, String)

holds : Store -> Location TestEnc -> String
holds s l = fromMaybe (place l) (lookup (place l) s)

||| The moves run one at a time.
run : List (Instr TestEnc) -> Store -> Store
run [] s = s
run (Move d x :: is) s = run is ((place d, holds s x) :: s)
run (_ :: is) s = run is s

||| Whether the moves do what the parallel move means: each destination
||| holds what its source held, every other place of the move what it held.
agrees : List (Location TestEnc, Location TestEnc) -> List (Instr TestEnc) -> Bool
agrees ms is =
  let after = run is []
      dests = map fst ms
  in all (\(d, x) => holds after d == place x) ms
     && all (\l => any (\d => place d == place l) dests || holds after l == place l) (map snd ms)

shown : Instr TestEnc -> String
shown (Move d x) = show d ++ " := " ++ show x
shown _ = "?"

cases : List (String, List (Location TestEnc, Location TestEnc))
cases =
  [ ("x to itself", [(word 0, word 0)])
  , ("a chain", [(word 1, word 2), (word 2, word 3)])
  , ("a swap", [(word 1, word 2), (word 2, word 1)])
  , ("a cycle of three", [(word 1, word 2), (word 2, word 3), (word 3, word 1)])
  , ("a cycle with a branch", [(word 1, word 2), (word 2, word 1), (word 3, word 1)])
  , ("two swaps", [(word 1, word 2), (word 2, word 1), (word 3, word 4), (word 4, word 3)])
  , ("a swap of doubles", [(double 1, double 2), (double 2, double 1)]) ]

covering
main : IO ()
main = for_ cases $ \(name, ms) => do
  let is = sequential cycleTemp ms
  putStrLn (name ++ ": " ++ (if agrees ms is then "agrees" else "DISAGREES"))
  for_ is $ \i => putStrLn ("  " ++ shown i)
