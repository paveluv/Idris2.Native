||| The foreign functions of `base`'s `Data.Buffer`, as the runtime
||| implements them, over buffers as it keeps them (`Support.BufferObj`),
||| each a flat function of the foreign one's name and type
||| (`Native.Support` says how they are bound). A number of
||| several bytes is little-endian; a signed one is read back with its
||| sign; a string is the system's text through `Support.Text`, for every
||| encoding. The program ends for bytes outside a buffer.
module Native.Support.Foreign.Data.Buffer

-- lint: allow layering: `Buffer` is `base`'s external type, which this
-- module's functions take and make; nothing of `base` runs here
import Data.Buffer
import Native.Flat.Uniform as Flat
import Native.Primitive.DoubleBits
import Native.Runtime.Memory
import Native.Runtime.Ordo as Runtime
import Native.Runtime.Raw as Runtime
import Native.Support.BufferObj
import Native.Support.Text

%hide Prelude.Interfaces.(>>=)
%hide Prelude.Interfaces.(>>)
%hide Prelude.Interfaces.pure

%default total

||| The signed value of a number of so many bits, whose sign bit `top` is:
||| the number less twice `top` when it has its sign bit set.
signed : (top, n : Bits64) -> Int
signed top n = if n >= top then cast n - 2 * cast top else cast n

%cg native flat Support.Foreign.Data.Buffer.prim__bufferSize
||| The buffer's bytes.
export
prim__bufferSize : Flat.Uniform Buffer -> Int
prim__bufferSize b = let (Runtime.MkOrdo # n) = BufferObj.size b Runtime.MkOrdo in cast n

%cg native flat Support.Foreign.Data.Buffer.prim__newBuffer
||| A new buffer of the bytes, all zero; `base` asks for no negative size.
export covering
prim__newBuffer : Int -> PrimIO (Flat.Uniform Buffer)
prim__newBuffer n w = let (Runtime.MkOrdo # b) =
                            BufferObj.zeroBuffer (cast (if n < 0 then 0 else n))
                              Runtime.MkOrdo in MkIORes b w

%cg native flat Support.Foreign.Data.Buffer.prim__setByte
||| The value's low byte stored in the buffer at the offset.
export
prim__setByte : Flat.Uniform Buffer -> (offset : Int) -> Int -> PrimIO ()
prim__setByte b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 1 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getByte
||| The byte, from 0 to 255, in the buffer at the offset.
export
prim__getByte : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Int
prim__getByte b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 1 b offset Runtime.MkOrdo
  in MkIORes (cast n) w

%cg native flat Support.Foreign.Data.Buffer.prim__setBits8
||| The `Bits8` stored in the buffer at the offset.
export
prim__setBits8 : Flat.Uniform Buffer -> (offset : Int) -> Bits8 -> PrimIO ()
prim__setBits8 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 1 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getBits8
||| The `Bits8` in the buffer at the offset.
export
prim__getBits8 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Bits8
prim__getBits8 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 1 b offset Runtime.MkOrdo
  in MkIORes (cast n) w

%cg native flat Support.Foreign.Data.Buffer.prim__setBits16
||| The `Bits16` stored in the buffer at the offset, its 2 bytes.
export
prim__setBits16 : Flat.Uniform Buffer -> (offset : Int) -> Bits16 -> PrimIO ()
prim__setBits16 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 2 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getBits16
||| The `Bits16` in the buffer at the offset.
export
prim__getBits16 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Bits16
prim__getBits16 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 2 b offset Runtime.MkOrdo
  in MkIORes (cast n) w

%cg native flat Support.Foreign.Data.Buffer.prim__setBits32
||| The `Bits32` stored in the buffer at the offset, its 4 bytes.
export
prim__setBits32 : Flat.Uniform Buffer -> (offset : Int) -> Bits32 -> PrimIO ()
prim__setBits32 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 4 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getBits32
||| The `Bits32` in the buffer at the offset.
export
prim__getBits32 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Bits32
prim__getBits32 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 4 b offset Runtime.MkOrdo
  in MkIORes (cast n) w

%cg native flat Support.Foreign.Data.Buffer.prim__setBits64
||| The `Bits64` stored in the buffer at the offset, its 8 bytes.
export
prim__setBits64 : Flat.Uniform Buffer -> (offset : Int) -> Bits64 -> PrimIO ()
prim__setBits64 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 8 b offset v Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getBits64
||| The `Bits64` in the buffer at the offset.
export
prim__getBits64 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Bits64
prim__getBits64 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 8 b offset Runtime.MkOrdo
  in MkIORes n w

%cg native flat Support.Foreign.Data.Buffer.prim__setInt8
||| The `Int8` stored in the buffer at the offset.
export
prim__setInt8 : Flat.Uniform Buffer -> (offset : Int) -> Int8 -> PrimIO ()
prim__setInt8 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 1 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getInt8
||| The `Int8` in the buffer at the offset.
export
prim__getInt8 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Int8
prim__getInt8 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 1 b offset Runtime.MkOrdo
  in MkIORes (cast (signed 0x80 n)) w

%cg native flat Support.Foreign.Data.Buffer.prim__setInt16
||| The `Int16` stored in the buffer at the offset, its 2 bytes.
export
prim__setInt16 : Flat.Uniform Buffer -> (offset : Int) -> Int16 -> PrimIO ()
prim__setInt16 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 2 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getInt16
||| The `Int16` in the buffer at the offset.
export
prim__getInt16 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Int16
prim__getInt16 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 2 b offset Runtime.MkOrdo
  in MkIORes (cast (signed 0x8000 n)) w

%cg native flat Support.Foreign.Data.Buffer.prim__setInt32
||| The `Int32` stored in the buffer at the offset, its 4 bytes.
export
prim__setInt32 : Flat.Uniform Buffer -> (offset : Int) -> Int32 -> PrimIO ()
prim__setInt32 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 4 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getInt32
||| The `Int32` in the buffer at the offset.
export
prim__getInt32 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Int32
prim__getInt32 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 4 b offset Runtime.MkOrdo
  in MkIORes (cast (signed 0x80000000 n)) w

%cg native flat Support.Foreign.Data.Buffer.prim__setInt64
||| The `Int64` stored in the buffer at the offset, its 8 bytes.
export
prim__setInt64 : Flat.Uniform Buffer -> (offset : Int) -> Int64 -> PrimIO ()
prim__setInt64 b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 8 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getInt64
||| The `Int64` in the buffer at the offset.
export
prim__getInt64 : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Int64
prim__getInt64 b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 8 b offset Runtime.MkOrdo
  in MkIORes (cast n) w

%cg native flat Support.Foreign.Data.Buffer.prim__setInt
||| The `Int` stored in the buffer at the offset, its 8 bytes.
export
prim__setInt : Flat.Uniform Buffer -> (offset : Int) -> Int -> PrimIO ()
prim__setInt b offset v w =
  let (Runtime.MkOrdo # ()) = BufferObj.store 8 b offset (cast v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getInt
||| The `Int` in the buffer at the offset.
export
prim__getInt : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Int
prim__getInt b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 8 b offset Runtime.MkOrdo
  in MkIORes (cast n) w

%cg native flat Support.Foreign.Data.Buffer.prim__setDouble
||| The `Double` stored in the buffer at the offset, its 8 bytes.
export
prim__setDouble : Flat.Uniform Buffer -> (offset : Int) -> Double -> PrimIO ()
prim__setDouble b offset v w =
  let (Runtime.MkOrdo # ()) =
        BufferObj.store 8 b offset (Primitive.DoubleBits.doubleBits v) Runtime.MkOrdo
  in MkIORes () w

%cg native flat Support.Foreign.Data.Buffer.prim__getDouble
||| The `Double` in the buffer at the offset.
export
prim__getDouble : Flat.Uniform Buffer -> (offset : Int) -> PrimIO Double
prim__getDouble b offset w =
  let (Runtime.MkOrdo # n) = BufferObj.load 8 b offset Runtime.MkOrdo
  in MkIORes (Primitive.DoubleBits.bitsDouble n) w

%cg native flat Support.Foreign.Data.Buffer.stringByteLength
||| The bytes of the string's text as the system's, which `setString`
||| stores.
export
stringByteLength : Flat.Uniform String -> Int
stringByteLength s = let (Runtime.MkOrdo # n) = Text.textBytes s Runtime.MkOrdo in cast n

%cg native flat Support.Foreign.Data.Buffer.prim__setString
||| The string's text, as the system's bytes, stored in the buffer from the
||| offset.
export covering
prim__setString : Flat.Uniform Buffer -> (offset : Int) -> Flat.Uniform String -> PrimIO ()
prim__setString b offset s w = let (Runtime.MkOrdo # ()) = setOp Runtime.MkOrdo in MkIORes () w
  where
    covering
    setOp : Runtime.Ordo.Op Runtime.Ordo ()
    setOp = do
      n <- Text.textBytes s
      to <- BufferObj.bytesAt b offset (cast n)
      Text.withText s (Runtime.Ordo.pure ()) (\p, k => Runtime.Memory.copyRaw p to k)

%cg native flat Support.Foreign.Data.Buffer.prim__getString
||| The string of the buffer's `len` bytes from the offset, as the system's
||| text.
export covering
prim__getString : Flat.Uniform Buffer -> (offset, len : Int) -> PrimIO (Flat.Uniform String)
prim__getString b offset len w = let (Runtime.MkOrdo # s) = getOp Runtime.MkOrdo in MkIORes s w
  where
    covering
    getOp : Runtime.Ordo.Op Runtime.Ordo (Flat.Uniform String)
    getOp = do
      p <- BufferObj.bytesAt b offset len
      Text.ofText p (cast len)

%cg native flat Support.Foreign.Data.Buffer.prim__copyData
||| `len` bytes of one buffer from its offset copied into another from
||| its, the same buffer too, the copy as if through a third.
export covering
prim__copyData : Flat.Uniform Buffer -> (srcOffset, len : Int) -> Flat.Uniform Buffer ->
                 (dstOffset : Int) -> PrimIO ()
prim__copyData src from len dst to w = let (Runtime.MkOrdo # ()) =
                                             copyOp Runtime.MkOrdo in MkIORes () w
  where
    covering
    copyOp : Runtime.Ordo.Op Runtime.Ordo ()
    copyOp = do
      p <- BufferObj.bytesAt src from len
      q <- BufferObj.bytesAt dst to len
      Runtime.Memory.copyRaw p q (cast len)
