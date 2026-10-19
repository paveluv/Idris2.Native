-- Random allocations and frees, checked: the driver both programs of this
-- test run, the model's on Chez and the native one on the system's memory.
--
-- A generator of 64-bit words (a linear congruential one, fixed seed)
-- chooses at each step whether to allocate or to free, and what: mostly
-- small blocks, of up to 128 bytes or up to the largest a slab holds, and
-- one in five a large block, a chunk of its own. The driver keeps the live
-- blocks by address, writes a tag into the first and the last word of each,
-- and checks, as it goes:
--
--   * that no block is null, and each is aligned to 16 bytes;
--   * that a new block overlaps no live one;
--   * that a block's tags are intact when it is freed, so that neither the
--     allocator nor another block wrote into it.
--
-- At the end every live block is freed. What it counts depends on the
-- choices alone, not on the addresses, so both programs print the same.
module Driver

import Data.List
import Data.Maybe
import Data.SortedMap

%default covering

||| The allocator under test, and the memory its blocks are in.
public export
record Ops where
  constructor MkOps
  alloc : Bits64 -> IO Bits64
  free : Bits64 -> IO ()
  load : Bits64 -> IO Bits64
  store : Bits64 -> Bits64 -> IO ()

public export
record Tally where
  constructor MkTally
  allocs, frees, nulls, misaligned, overlaps, corrupted : Nat

export
Show Tally where
  show t = show t.allocs ++ " allocations, " ++ show t.frees ++ " frees, " ++ show t.nulls
    ++ " null, "
           ++ show t.misaligned ++ " misaligned, " ++ show t.overlaps ++ " overlapping, "
             ++ show t.corrupted ++ " corrupted"

nextWord : Bits64 -> Bits64
nextWord s = s * 6364136223846793005 + 1442695040888963407

-- the size of a request, from a word of the generator
sizeOf : (large : Bits64) -> Bits64 -> Bits64
sizeOf large r =
  let v = prim__shr_Bits64 r 20 in
  if r `mod` 5 == 0 then large + 1 + v `mod` (40 * large)
  else 1 + v `mod` (if r `mod` 3 == 0 then large else 128)

-- the offset of a block's last word, for a request of `n` bytes
lastWord : Bits64 -> Bits64
lastWord n = if n <= 8 then 0 else ((n - 8) `div` 8) * 8

Live : Type
Live = SortedMap Bits64 (Bits64, Bits64)

overlapping : Live -> (addr, n : Bits64) -> Bool
overlapping live a n =
  let (left, right) = lookupBetween a live in
  isJust (lookup a live) || before left || after right
  where
    before : Maybe (Bits64, (Bits64, Bits64)) -> Bool
    before (Just (b, (m, _))) = b + m > a
    before Nothing = False

    after : Maybe (Bits64, (Bits64, Bits64)) -> Bool
    after (Just (b, _)) = b < a + n
    after Nothing = False

allocate : Ops -> Live -> Tally -> (n, tag : Bits64) -> IO (Live, Tally)
allocate ops live t n tag = do
  a <- ops.alloc n
  if a == 0 then pure (live, { allocs $= S, nulls $= S } t) else do
    let t' = { allocs $= S, misaligned $= (if a `mod` 16 == 0 then id else S),
               overlaps $= (if overlapping live a n then S else id) } t
    ops.store a tag
    ops.store (a + lastWord n) tag
    pure (insert a (n, tag) live, t')

release : Ops -> Live -> Tally -> (addr : Bits64) -> IO (Live, Tally)
release ops live t a = case lookup a live of
  Nothing => pure (live, t)
  Just (n, tag) => do
    x <- ops.load a
    y <- ops.load (a + lastWord n)
    ops.free a
    pure (delete a live, { frees $= S, corrupted $= (if x == tag && y == tag then id else S) } t)

steps : Ops -> (large : Bits64) -> Live -> Tally -> (seed : Bits64) -> (left : Nat) ->
        IO (Live, Tally)
steps ops large live t s Z = pure (live, t)
steps ops large live t s (S k) = do
  let s' = nextWord s
      r = prim__shr_Bits64 s' 11
      count = length (keys live)
  (live', t') <- if count == 0 || (r `mod` 10 < 6 && count < 200)
    then allocate ops live t (sizeOf large r) s'
    else release ops live t (fromMaybe 0 (head' (drop (cast (r `mod` cast count)) (keys live))))
  steps ops large live' t' s' k

||| The run: `n` steps from the seed, then every live block freed.
export
run : Ops -> (large : Bits64) -> (seed : Bits64) -> (n : Nat) -> IO Tally
run ops large seed n = do
  (live, t) <- steps ops large empty (MkTally 0 0 0 0 0 0) seed n
  freeAll (keys live) live t
  where
    freeAll : List Bits64 -> Live -> Tally -> IO Tally
    freeAll [] _ t = pure t
    freeAll (a :: as) live t = do
      (live', t') <- release ops live t a
      freeAll as live' t'
