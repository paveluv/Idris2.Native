-- The allocator against a model of the system's memory, on Chez: the
-- property test. The model keeps the words stored and the pages committed;
-- a load or a store outside a committed page is a fault, which the
-- allocator must never make. Pages it commits read as zero, and pages it
-- releases are forgotten, so that memory it gave back and reads again
-- shows.
--
-- The configuration is small, so that every path runs often: blocks of 16
-- bytes to 1 KiB in slabs, granules of 4 KiB, chunks up to 64 KiB, a region
-- of 4 MiB. The driver (`Driver`) runs three times from the same seed.
-- After the first run, with every block freed, the region the arena took
-- and the pages left committed show that empty slabs and large blocks went
-- back: what stays is the control block, the pagemap's entries for the
-- region taken, and the two empty slabs each class keeps. The second run
-- takes a little more of the region: the slabs kept split chunks that the
-- largest blocks of the first run had whole. The third takes none: freed
-- memory is reused, and the region stops growing.
module Main

import Data.IORef
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Driver
import Native.Runtime.Alloc.Allocator
import Native.Runtime.Alloc.Arena
import Native.Runtime.Alloc.Chunks
import Native.Runtime.Alloc.Config
import Native.Runtime.Alloc.Pages
import Native.Runtime.Alloc.SizeClasses
import Native.Runtime.Heap

%default covering

record Space where
  constructor MkSpace
  words : SortedMap Bits64 Bits64
  pages : SortedSet Bits64
  next : Bits64
  faults : Nat

-- The model's token, linear, whose space is unrestricted once matched.
data Model : Type where
  MkModel : Space -> Model

page : Bits64
page = 4096

pageOf : Bits64 -> Bits64
pageOf a = a - a `mod` page

-- the pages from an address, for a count of bytes
pagesIn : (addr, bytes : Bits64) -> List Bits64
pagesIn a n = if n == 0 then [] else [ a + page * cast i | i <- [0 .. cast ((n - 1) `div` page)] ]

-- the words of the pages forgotten
forget : List Bits64 -> SortedMap Bits64 Bits64 -> SortedMap Bits64 Bits64
forget ps ws = foldl (\m, p => foldl (\m', i => delete (p + 8 * cast i) m') m [the Nat 0 .. 511]) ws ps

Pages Model where
  reserve n (MkModel s) = MkModel ({ next := s.next + n + page } s) # s.next
  commit a n (MkModel s) =
    let ps = pagesIn a n in
    MkModel ({ pages $= \set => foldl (flip insert) set ps, words $= forget ps } s) # True
  release a n (MkModel s) =
    let ps = pagesIn a n in
    MkModel ({ pages $= \set => foldl (flip delete) set ps, words $= forget ps } s) # ()
  pageBytes m = m # page
  load a o (MkModel s) =
    if contains (pageOf (a + o)) s.pages
       then MkModel s # fromMaybe 0 (lookup (a + o) s.words)
       else MkModel ({ faults $= S } s) # 0
  store a o v (MkModel s) =
    if contains (pageOf (a + o)) s.pages
       then MkModel ({ words $= insert (a + o) v } s) # ()
       else MkModel ({ faults $= S } s) # ()

small : Config
small = MkConfig 4 2 10 12 16 22 2

-- an operation of the model run on the model in the reference
on : IORef Model -> Op Model a -> IO a
on ref f = do
  m <- readIORef ref
  let (m' # v) = f m
  writeIORef ref m'
  pure v

ops : IORef Model -> SizeClasses Buddy -> Ops
ops ref s = MkOps (\n => on ref (allocate s n)) (\a => on ref (free s a))
                  (\a => on ref (load a 0)) (\a, v => on ref (store a 0 v))

space : IORef Model -> IO Space
space ref = do
  MkModel s <- readIORef ref
  pure s

main : IO ()
main = do
  ref <- newIORef (MkModel (MkSpace empty empty 0x10000000 0))
  a <- on ref (newArena small)
  let s = MkSizeClasses small a (MkBuddy small a)
  t1 <- run (ops ref s) 1024 7 20000
  putStrLn ("model, first run: " ++ show t1)
  start <- on ref (field a 1)
  taken1 <- on ref (field a 3)
  sp1 <- space ref
  putStrLn ("the region taken: " ++ show (taken1 - start) ++ " bytes; pages committed with every block freed: "
            ++ show (length (Prelude.toList sp1.pages)))
  t2 <- run (ops ref s) 1024 7 20000
  putStrLn ("model, second run: " ++ show t2)
  taken2 <- on ref (field a 3)
  t3 <- run (ops ref s) 1024 7 20000
  putStrLn ("model, third run: " ++ show t3)
  taken3 <- on ref (field a 3)
  sp3 <- space ref
  putStrLn ("the region taken grew by " ++ show (taken2 - taken1) ++ " bytes in the second run, by "
            ++ show (taken3 - taken2) ++ " in the third; faults: " ++ show sp3.faults)
