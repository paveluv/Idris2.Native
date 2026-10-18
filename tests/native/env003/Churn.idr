-- One variable set a million times, natively, in bounded memory: each
-- `setEnv` makes a new entry, `NAME=value` and a zero byte, in a block of
-- memory outside the heap, and frees the entry it replaces. The run limits
-- the process's data to 32 MiB, against the 128 MiB that a million entries
-- of more than 100 bytes would take if the replaced ones were kept, as the
-- C library keeps them.
--
-- The runtime can free them because nothing holds a pointer into one past
-- the call that gave it: `base`'s `getEnv` copies the value at once,
--
--     getEnv var = do env <- primIO (prim__getEnv var)
--                     if prim__nullPtr env /= 0 then pure Nothing
--                                               else pure (Just (prim__getString env))
--
-- and no C code is linked to keep one.
module Main

import Data.String
import System

-- the variable set `n` times, each value 100 bytes and the count; whether
-- every `setEnv` succeeded
churn : Int -> IO Bool
churn 0 = pure True
churn n = do
  ok <- setEnv "IDR_CHURN" (replicate 100 'v' ++ show n) True
  if ok then churn (n - 1) else pure False

main : IO ()
main = do
  ok <- churn 1000000
  putStrLn ("every setEnv succeeded: " ++ show ok)
  v <- getEnv "IDR_CHURN"
  putStrLn ("the last value's length: " ++ show (map length v))
