-- References through Data.IORef, printed: a counter written a thousand
-- times, a reference to a list that grows by one cons per write, a reference
-- to a reference, and a hundred references made, written and read in turn.
--
-- A reference is an object of one uniform value. `newIORef v` allocates it
-- holding `v`, `readIORef r` loads its value, `writeIORef r v` stores over
-- it: the object stays where it is, and what it holds changes. Under a
-- tiny allocation window the conses the list's writes allocate fill the
-- window again and again, so the collector runs while the reference, made
-- long before, holds the newest of them: the reference must be found and
-- its value moved with the rest.
module Main

import Data.IORef
import Data.List

-- the counter: r := r + i for i from 1 to n
count : IORef Int -> Int -> Int -> IO ()
count r i n =
  if i > n then pure ()
  else do v <- readIORef r
          writeIORef r (v + i)
          count r (i + 1) n

-- the list: r := i :: r for i from 1 to n
grow : IORef (List Int) -> Int -> Int -> IO ()
grow r i n =
  if i > n then pure ()
  else do modifyIORef r (i ::)
          grow r (i + 1) n

-- a hundred references, the k-th made holding k, then each doubled
refs : Int -> IO (List (IORef Int))
refs k = if k > 100 then pure [] else do
  r <- newIORef k
  rest <- refs (k + 1)
  pure (r :: rest)

main : IO ()
main = do
  counter <- newIORef 0
  count counter 1 1000
  printLn !(readIORef counter)
  list <- newIORef []
  grow list 1 300
  xs <- readIORef list
  printLn (length xs, sum xs, take 3 xs)
  inner <- newIORef "first"
  outer <- newIORef inner
  writeIORef !(readIORef outer) "second"
  putStrLn !(readIORef inner)
  rs <- refs 1
  traverse_ (\r => modifyIORef r (* 2)) rs
  vs <- traverse readIORef rs
  printLn (sum vs, take 3 vs)
