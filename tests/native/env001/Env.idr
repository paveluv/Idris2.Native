-- The program's environment, natively: `getEnv` finds a variable among the
-- entries the system put after the arguments, each `NAME=value`, and gives
-- its value, copied into a new string, or `Nothing` for a name no entry
-- has. A name is compared with an entry's bytes up to the `=`, so `IDR`
-- does not find `IDRX=...`, nor `IDRX` find `IDR=...`; an empty value is
-- a value; a name with `=` in it, or the empty name, finds none. The
-- Chez backend gives the same, through the C library's `getenv`.
--
-- `getEnv` asks the runtime for a pointer to the value's bytes, `Nothing`
-- when the pointer is null, then copies the bytes the pointer points to:
-- in surface Idris, base's
--
--     getEnv var = do env <- primIO (prim__getEnv var)
--                     if prim__nullPtr env /= 0 then pure Nothing
--                                               else pure (Just (prim__getString env))
module Main

import System

main : IO ()
main = traverse_ (\n => putStrLn (n ++ ": " ++ show !(getEnv n)))
  ["IDR", "IDRX", "IDR_EMPTY", "IDR_UTF8", "IDR_NONE", "", "IDR=one"]
