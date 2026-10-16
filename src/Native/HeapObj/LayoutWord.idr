||| The layout word of a continuation's resume point (`layoutWord`), and
||| what the collector reads of it.
|||
||| Part of the heap-object model, the contract between compiled code and
||| the runtime (`HeapObj.Shape` says what it is): it imports nothing from the
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

||| A layout word's live values.
export
layoutValues : (layout : Bits64) -> Bits64
layoutValues l = prim__and_Bits64 l 0xFFFFFF

||| A layout word's live raw words.
export
layoutRaws : (layout : Bits64) -> Bits64
layoutRaws l = prim__and_Bits64 (prim__shr_Bits64 l 24) 0xFFFFFF

||| A continuation's words, by its layout word: the resume address, the
||| parent, the values, then the raw words.
export
continuationWords : (layout : Bits64) -> Bits64
continuationWords l = 2 + layoutValues l + layoutRaws l

||| The words of a continuation that hold values: its parent and the live
||| values.
export
continuationScanned : (layout : Bits64) -> (Bits64, Bits64)
continuationScanned l = (1, 1 + layoutValues l)
