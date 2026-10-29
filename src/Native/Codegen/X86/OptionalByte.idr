||| A byte that an instruction may have or not (`OptionalByte`), such as its
||| REX prefix or its SIB byte: one part of Intel's instruction format
||| (`Native.Codegen.X86.InstrFormat`), read as the instruction is, for the
||| bytes it takes, its bytes, or its bytes written through a span.
module Native.Codegen.X86.OptionalByte

import Data.Bits
import Native.Codegen.ByteSink

%default total

||| A byte or none, held as a number: the byte with bit 8 set when there is
||| one, 0 when there is none, so that an instruction's optional bytes make
||| no object of their own. Abstract: made by `none` and `byte`.
export
record OptionalByte where
  constructor MkOptionalByte
  code : Int

||| No byte.
export
none : OptionalByte
none = MkOptionalByte 0

||| This byte.
export
byte : Bits8 -> OptionalByte
byte b = MkOptionalByte (0x100 .|. cast b)

||| The bytes taken by a byte or none, by whether there is none.
taken : (none : Bool) -> Nat
taken True = 0
taken False = 1

||| The bytes it takes: 1 for a byte, 0 for none.
export
size : OptionalByte -> Nat
size o = taken (o.code == 0)

||| The byte, if there is one.
export
bytes : OptionalByte -> List Bits8
bytes o = if o.code == 0 then [] else [cast o.code]

||| The byte written at the span's next byte, if there is one. Inlined:
||| a function whose body calls another that gives an action Idris
||| compiles as one that makes an action, at each write.
export %inline
write : (s : ByteSink.Sink) -> (o : OptionalByte) -> ByteSink.Span s (size o + n) ->
        IO (ByteSink.Span s n)
write s o sp = byNone (o.code == 0) sp
  where
    -- by whether there is none, which the bytes it takes are of (`taken`)
    byNone : (none : Bool) -> ByteSink.Span s (taken none + n) -> IO (ByteSink.Span s n)
    byNone True sp = pure sp
    byNone False sp = ByteSink.putBits8 s sp (cast o.code)
