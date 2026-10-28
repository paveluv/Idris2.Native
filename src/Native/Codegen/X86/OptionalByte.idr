||| A byte that an instruction may have or not (`OptionalByte`), such as its
||| REX prefix or its SIB byte: one part of Intel's instruction format
||| (`Native.Codegen.X86.InstrFormat`), read as the instruction is, for the
||| bytes it takes, its bytes, or its bytes written through a sink.
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

||| The bytes it takes: 1 for a byte, 0 for none.
export
size : OptionalByte -> Nat
size o = if o.code == 0 then 0 else 1

||| The byte, if there is one.
export
bytes : OptionalByte -> List Bits8
bytes o = if o.code == 0 then [] else [cast o.code]

||| The byte written at the sink's next offset, if there is one, and if it
||| fits before the sink's end.
export
put : ByteSink.Sink -> OptionalByte -> IO (Maybe ByteSink.Sink)
put s o = if o.code == 0 then pure (Just s) else ByteSink.putBits8 s (cast o.code)
