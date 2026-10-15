||| The layout word of a continuation's resume point (`layoutWord`).
|||
||| Part of the heap-object model, the contract between compiled code and
||| the runtime (`HeapObj.Enc` says what it is): it imports nothing from the
||| compiler, so that the runtime's own Idris can import it.
module Native.HeapObj.LayoutWord

%default total

||| The layout word that precedes every resume point in the text: the number
||| of live `Val`s in bits 0..23, of live raw words in bits 24..47, and the
||| magic 0x1DC0 in bits 48..63. A continuation has no header word; its first
||| word is its resume address, and the word before that address gives its
||| size (`CONT`).
public export
layoutWord : (nval, nraw : Integer) -> Integer
layoutWord nval nraw = 0x1DC0000000000000 + nraw * 0x1000000 + nval
