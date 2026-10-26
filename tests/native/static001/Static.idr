-- Constants marked static. A directive of the native code generator,
--
--   %cg native static Main.squares Main.successors Main.agreed Main.unread
--
-- names constants whose values the code generator computes as it compiles
-- the program, by evaluating Idris's compiled form of each, as the
-- program would compute it at run time. So far it does so only to check
-- that it can, and refuses a mark it cannot compute (the other modules of
-- this test): the program still computes each constant on its first use,
-- as any constant. Every code generator prints the same, so the expected
-- output holds the same lines three times: native, Chez, and native under
-- the encoding whose pointers carry a tag.
module Main

import Data.IORef
import Native.Types.Bytes

%default covering

%cg native static Main.squares Main.successors Main.agreed Main.unread

-- Eight words made by `generate`, the maker of a `Bytes`
-- (`Native.Types.FromWords`). Its body makes a buffer by a foreign
-- function, which only the running program can run, so the evaluation
-- never runs it: the maker's mark says what a call of it is, the object of
-- the words its function gives, here
--
--   squares = <the words 0, 1, 4, 9, 16, 25, 36, 49>
squares : Bytes
squares = generate 8 (\i => cast (i * i))

-- Words read from another constant's. The evaluation reads a word of
-- `squares` as the load does, at the sum of the row and the word in it:
-- `uncheckedWord squares 0 i`, word `i` of the row at 0, is the word at
-- `0 + i`, so
--
--   successors = <the words 1, 2, 5, 10, 17, 26, 37, 50>
--
-- `squares` is evaluated once, for itself and for this, in steps of its
-- own (the module `Fuel`).
successors : Bytes
successors = generate 8 (\i => uncheckedWord squares 0 i + 1)

-- A check of the evaluation's words, made as the program is compiled:
-- marked too, so evaluated with the others. Were the words not these, its
-- crash would end the compilation, as it does for a copy of this program
-- that expects another last word (the run script); as they are, it is
-- the string, which the program prints.
agreed : String
agreed =
  if map (\i => uncheckedWord successors i 0) [0 .. 7] == [1, 2, 5, 10, 17, 26, 37, 50]
    then "the words agree"
    else assert_total (idris_crash "the words disagree")

-- A mark of a constant no use reads. Computed, it would be refused, as
-- it makes a reference, which only the running program can (the module
-- `Extern`). But the evaluation computes only the marks the program
-- reaches, and from `main` nothing reaches `unread`, so it is not
-- computed, and the program is compiled all the same.
unread : IORef Int
unread = unsafePerformIO (newIORef 0)

main : IO ()
main = do
  printLn (map (\i => uncheckedWord squares i 0) [0 .. 7])
  printLn (map (\i => uncheckedWord successors i 0) [0 .. 7])
  putStrLn agreed
