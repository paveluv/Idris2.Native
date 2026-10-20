-- Top-level constants, natively: a definition of no arguments that Idris
-- finds constant is evaluated once, on its first use, and its value kept
-- in a cell of its own, which the collector forwards as a root. So the
-- one `IORef` below is shared by every use of `counter`, as it is on
-- Chez, and the list `table` survives the collections `churn` makes, in
-- a window of 4 KiB, so that there are hundreds.
--
-- In surface Idris, each use of a constant is a call:
--
--     main = do modifyIORef counter (+ 1) ...
--
-- calls `counter`, whose value the code generator gives from its cell
-- once the first call has computed it. Idris's own common-subexpression
-- pass makes such constants too, `modifyIORef counter (+ 1)` among them
-- here, which it lifts to the top level once it appears twice.
--
-- `onBranch` is used only where the program has more than five arguments:
-- it is never evaluated, and "on a branch" never printed. Chez evaluates
-- every constant the program reaches before `main`, and would print it.
module Main

import Data.IORef
import Native.Runtime.Space
import System

table : List Integer
table = unsafePerformIO (do putStrLn "table built"; pure [1 .. 2000])

counter : IORef Int
counter = unsafePerformIO (do putStrLn "counter made"; newIORef 0)

onBranch : Int
onBranch = unsafePerformIO (do putStrLn "on a branch"; pure 1)

-- many short-lived lists, so that the heap is collected many times
churn : Nat -> Nat -> Nat
churn Z acc = acc
churn (S k) acc = churn k (acc + length [1 .. the Integer 300])

main : IO ()
main = do
  printLn (sum table)
  modifyIORef counter (+ 1)
  printLn (churn 3000 0)
  modifyIORef counter (+ 1)
  printLn (churn 3000 0)
  args <- getArgs
  if length args > 5 then printLn onBranch else pure ()
  printLn (sum table, !(readIORef counter))
  c <- collectionCount
  putStrLn ("collected: " ++ show (c > 100))
