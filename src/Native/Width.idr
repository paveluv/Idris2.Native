||| How much of a word a value or a memory access takes (`Width`): all of
||| it, or its low 8, 16 or 32 bits (`SubWord`).
|||
||| One type serves both: an integer narrower than the word is held in a
||| word, extended from its width, and a narrow load or store moves the low
||| bits of a word. The machine types' widths are `Mach.width`'s.
|||
||| Part of the contract between compiled code and the runtime, with the
||| heap-object model (`HeapObj.Shape` says what it is).
module Native.Width

%default total

||| The narrow widths: 8, 16 and 32 bits, of an integer, of an extension
||| (`Ext`), of a narrow load or store (`LoadN`, `StoreN`).
public export
data SubWord = Sub8 | Sub16 | Sub32

||| A sub-word's width in bytes: the unit of a `LoadN` or `StoreN` index.
public export
subWordBytes : SubWord -> Nat
subWordBytes Sub8 = 1
subWordBytes Sub16 = 2
subWordBytes Sub32 = 4

||| How much of a word: its low bits, or all of it.
public export
data Width = Narrow SubWord | Whole
