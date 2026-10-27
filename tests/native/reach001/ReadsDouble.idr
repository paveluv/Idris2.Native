-- A program that reads a double, and shows none, with one constant marked
-- static of its own, `squares`, as `NoDouble`'s. It reads its first
-- argument, or "2.5" without one, as a double, multiplies it by a word of
-- `squares` and prints the product as an `Int`: `cast {to = Double} s` of
-- a string is one primitive, which the lowering makes a call of the
-- string routine `readDouble`. That routine rounds a decimal with both
-- of the runtime's tables of powers of ten, `exactPowerOfTen` on
-- Clinger's fast path and `powerOfTen` otherwise, each a constant marked
-- static, so the code generator computes both as it compiles the
-- program, and lays out their objects before `squares`', whose name comes
-- after theirs. The cast back to an `Int` and its `show` call no routine
-- that reads a table.
module Main

import Native.Types.Bytes
import System

%default covering

%cg native static Main.squares

-- Words a maker made, as if written
--
--   squares = <a BYTES object: its header, then the words 0, 1, 4, ..., 49>
squares : Bytes
squares = generate 8 (\i => cast (i * i))

main : IO ()
main = do
  -- the first argument, or "2.5", which only the running program knows
  s <- pure (case !getArgs of (_ :: a :: _) => a; _ => "2.5")
  printLn (cast {to = Int} (cast {to = Double} s * cast (uncheckedWord squares 3 0)))
