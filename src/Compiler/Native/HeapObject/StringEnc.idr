||| How a `String` is laid out (`StringEnc`), one of the program's
||| encodings (`Compiler.Native.HeapObject.Enc`).
|||
||| Part of the heap-object model, the contract between compiled code and the
||| runtime (`Compiler.Native.HeapObject.Enc` says what it is): it imports
||| nothing from the compiler, so that the runtime's own Idris can import it.
module Compiler.Native.HeapObject.StringEnc

%default total

||| How a `String` is laid out: its payload, and the parts of its header.
||| Every `STRING` holds a well-formed encoding of a sequence of Unicode
||| scalar values (no surrogates, nothing above U+10FFFF, and for UTF-8 the
||| shortest form), which every operation that makes a string keeps and every
||| one that reads it relies on. Code that branches on the encoding matches
||| every constructor, with no catch-all, so that another encoding is a
||| constructor the typechecker finds every place for.
public export
data StringEnc
  = ||| The UTF-8 bytes, and a header bit set exactly when every byte is
    ||| below 0x80, which turns the code-point operations of an ASCII string
    ||| into byte operations.
    Utf8
  | ||| One 32-bit code point per character, Chez's layout.
    Utf32

||| The string encodings under which a `StringH` exists, with the proof.
public export
data Utf8Strings : StringEnc -> Type where
  IsUtf8 : Utf8Strings Utf8

||| The string encodings under which a `StringCharsH` exists.
public export
data Utf32Strings : StringEnc -> Type where
  IsUtf32 : Utf32Strings Utf32
