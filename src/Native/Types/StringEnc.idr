||| How a `String` is laid out (`StringEnc`), one of the program's encodings
||| (`Types.Enc`).
|||
||| Part of the type layer, the modules of `Types` (`Types.Kind` says what
||| it is): it imports nothing from the compiler, so that the runtime's own
||| Idris can import it.
module Native.Types.StringEnc

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

||| The parts of a UTF-8 string's header: whether every byte is below
||| 0x80, and how many bytes there are.
public export
record Utf8Parts where
  constructor MkUtf8Parts
  ascii : Bool
  bytes : Nat

||| The part of a UTF-32 string's header: how many characters there are.
public export
record Utf32Parts where
  constructor MkUtf32Parts
  chars : Nat

||| The parts of a string's header under the encoding: what varies by the
||| encoding is the encoding's, so another encoding is a case here, not a
||| constructor of the header (`Types.Header.StringH`).
public export
StringParts : StringEnc -> Type
StringParts Utf8 = Utf8Parts
StringParts Utf32 = Utf32Parts
