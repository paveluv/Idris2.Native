-- Constants marked static whose values hold one value twice: natively the
-- image holds each value once, as `Static`'s equal rows are one object.
--
-- `tree` is a tree whose two subtrees, at each node, are one value, which
-- a `let` shares: 64 nodes deep, so 2^64 leaves, which the evaluation
-- makes as 64 nodes, as the program does at run time. The code generator
-- lays it out as 64 objects, each node once, however many paths lead to
-- it: a walk of every path would not end.
--
-- `twins` is a pair of two objects that makers made (`Bytes`), each by a
-- function of its own, whose words are equal: one object in the image,
-- whose address both fields hold.
--
-- Each is compared with the same value made as the program runs, and
-- every code generator prints the same: native, Chez, and native under
-- the encoding whose pointers carry a tag.
module Main

import Native.Types.Bytes
import System

%default covering

%cg native static Main.tree Main.twins

-- A binary tree.
data Tree = Leaf | Node Tree Tree

-- The tree of depth `k` whose two subtrees, at each node, are one value:
-- `k` nodes, however many leaves it has.
doubled : Nat -> Tree
doubled Z = Leaf
doubled (S k) = let half = doubled k in Node half half

-- As if written
--
--   tree = <a node, both its fields the address of the node below it, ...>
--
-- 64 objects, the last one's fields both the object every `Leaf` is.
tree : Tree
tree = doubled 64

-- Two objects makers made of the words 0, 1, 4, ..., 49, as if written
--
--   twins = (<a BYTES object: its header, then the words 0, 1, ..., 49>,
--            <the same object>)
twins : (Bytes, Bytes)
twins = (generate 8 (\i => cast (i * i)), generate 8 (\i => cast i * cast i))

-- Reads of `tree` and `twins`, by which the test finds their objects in
-- the image, each the address of its constant's first object, as
-- `Static`'s readers.
treeFrom : Int -> Tree
treeFrom _ = tree

twinsFrom : Int -> (Bytes, Bytes)
twinsFrom _ = twins

-- How deep a tree is along its left subtrees, and along its right ones,
-- which walk one path each.
leftDepth, rightDepth : Tree -> Nat
leftDepth Leaf = 0
leftDepth (Node l _) = S (leftDepth l)
rightDepth Leaf = 0
rightDepth (Node _ r) = S (rightDepth r)

-- The first eight words.
words : Bytes -> List Bits64
words b = map (\i => uncheckedWord b i 0) [0 .. 7]

main : IO ()
main = do
  -- 1, which only the running program knows, so that what is made from
  -- it below is made as the program runs
  n <- pure (length !getArgs)
  let made = doubled (63 + n)
  let read = treeFrom 0
  printLn (leftDepth read, rightDepth read)
  printLn (leftDepth read == leftDepth made, rightDepth read == rightDepth made)
  let squares = generate (cast (7 + n)) (\i => cast (i * i))
  let (first, second) = twinsFrom 0
  printLn (words first, words first == words squares, words second == words squares)
