-- Flat code becomes Direct functions, machine functions of the native
-- backend, and each keeps its values in a frame of its own on the machine
-- stack, as C does, so that a call leaves its caller's values where they
-- are: in
--
--   mix a b c d = let p = step a b      -- a, c and d are live across the call
--                     q = step c d      -- a, c and p are
--                 in step p q + a + c   -- a and c are
--
-- each `step` writes only its own frame, below `mix`'s, and `mix` saves
-- nothing around its calls: its listing has no push and no pop. Ordinary
-- code keeps its values across a call in the continuation it allocates, on
-- the heap, and its registers in SCRATCH, which no flat function writes.
module Main

import System

-- `step` calls itself, a loop for a large `y`, so it is no small form,
-- which flat code would take in place of the call (`Native.Flat.Inline`),
-- and `mix`'s calls stay calls
%cg native flat Main.step
step : Bits64 -> Bits64 -> Bits64
step x y = if y >= 1000 then step x (y - 1000) else x * 31 + y

%cg native flat Main.mix
mix : Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64
mix a b c d =
  let p = step a b
      q = step c d
  in step p q + a + c

-- Not inlined, so the arguments are known only at run time.
%noinline
given : Bits64 -> Bits64
given x = x

main : IO ()
main = do
  -- step 1 2 = 33, step 3 4 = 97, step 33 97 = 1120, + 1 + 3
  let r = mix (given 1) (given 2) (given 3) (given 4)
  putStrLn (show r)
  exitWith (if r == 1124 then ExitSuccess else ExitFailure 1)
