-- Immutable bytes on both code generators: words made once by ordinary
-- code, then read by a pure load from ordinary code and from flat code.
-- Chez runs the reader's body, its meaning: the buffer's word. The native
-- code generator never compiles the body: in flat code each read is one
-- load from the object, inline. They print the same, so the expected
-- output holds the same lines three times: native, Chez, and native under
-- the encoding whose pointers carry a tag.
--
-- A `Bytes` is a record of one field, a buffer, which every code generator
-- holds as the buffer itself; nothing writes it once `generate` gives it.
-- So a read needs no token: it may be done at any time.
module Main

import Native.Types.Bytes

%default covering

-- Word 1 of row `i`, a constant displacement: as if written
--
--   pick b i = load (b + 8 + 8 * i + 8 * 1)
--
-- one load, the displacement folded into the address.
%cg native flat Main.pick
pick : Bytes -> Int -> Bits64
pick b i = uncheckedWord b i 1

-- Word `d` of row `i`, a displacement known only at run time: the index
-- and the displacement added, then one load.
%cg native flat Main.at
at : Bytes -> Int -> Int -> Bits64
at b i d = uncheckedWord b i d

-- Word `i`, by a constant displacement too far to fold, 2^27 words: the
-- index and the displacement added, then one load, as `at`'s; the index
-- is `i - 2^27` so that the word read is word `i`.
%cg native flat Main.far
far : Bytes -> Int -> Bits64
far b i = uncheckedWord b (i - 0x8000000) 0x8000000

-- Word `i - 1`, by a negative constant displacement, folded as a positive
-- one is.
%cg native flat Main.before
before : Bytes -> Int -> Bits64
before b i = uncheckedWord b i (-1)

-- One of two `Bytes`, given back to ordinary code: one register in, one
-- out, the object as ordinary code holds it.
%cg native flat Main.choose
choose : Bool -> Bytes -> Bytes -> Bytes
choose c x y = if c then x else y

-- The sum of the first `n` words, wrapping as `Bits64` does: a loop of
-- loads, the `Bytes` in one register throughout.
%cg native flat Main.sumWords
sumWords : Bytes -> Int -> Bits64
sumWords b n = go 0 0
  where
    go : Int -> Bits64 -> Bits64
    go i acc = if i >= n then acc else go (i + 1) (acc + uncheckedWord b i 0)

main : IO ()
main = do
  -- six words, 7, 1007, ..., 5007, made by a function of ordinary code
  let b = generate 6 (\i => cast i * 1000 + 7)
  -- ordinary code reads through the boundary of the reader's flat form
  printLn (map (\i => uncheckedWord b i 0) [0 .. 5])
  printLn (map (pick b) [0 .. 4])
  printLn (map (\d => at b 2 d) [0 .. 3])
  printLn (sumWords b 6)
  printLn (map (far b) [0 .. 5], map (before b) [1 .. 5])
  -- words whose top two bits differ, which no fixnum holds: boxed as each
  -- leaves the reader for ordinary code (a word whose top two bits are
  -- the same, such as 0xFFFFFFFFFFFFFFFF, is -1, a fixnum)
  let big = generate 2 (\i => 0x8000000000000000 + cast i)
  printLn (uncheckedWord big 0 0, uncheckedWord big 0 1, pick big 0)
  -- no words, for a count of 0 and for one below it; a `Bytes` that flat
  -- code chose, read by ordinary code
  let none = generate 0 (\i => 1)
  let under = generate (-5) (\i => 1)
  printLn (sumWords none 0, sumWords under 0)
  printLn (uncheckedWord (choose True b big) 3 0, uncheckedWord (choose False b big) 1 0)
