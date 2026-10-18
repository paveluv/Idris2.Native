-- The terminal's size, natively: `getTermCols` and `getTermLines` ask the
-- system for the size of the terminal the standard input is, or else the
-- standard output, and answer 0 when neither is a terminal, as the Chez
-- backend's C support does. `setupTerm` comes first, as the compiler's
-- `main` calls it; on Linux a terminal takes escape sequences as it is, so
-- it changes nothing.
--
-- Run once with no terminal at all (the input /dev/null, the output a
-- pipe), then with the output a pseudo-terminal made 77 columns by 23
-- lines and the input still /dev/null, so that the answer comes from the
-- output.
module Main

import System.Term

main : IO ()
main = do
  setupTerm
  putStrLn ("columns " ++ show !getTermCols ++ ", lines " ++ show !getTermLines)
