||| How an allocator of memory outside the heap is configured (`Config`):
||| the sizes it hands out and the chunks it builds them from, all powers of
||| two given by their logarithms, and the rules that follow from them.
|||
||| A block is one of the size classes, four per doubling of size, so that
||| rounding a request up wastes at most a fifth of it: from the smallest
||| block in steps of it up to four of it (16, 32, 48, 64), then four steps
||| per doubling (80, 96, 112, 128, 160, ...), up to the largest a slab
||| holds. A larger request is a chunk of its own. A chunk is a power of two
||| of granules, aligned to its size, which the arena's buddy allocator
||| splits and joins; a slab is a chunk of one class's blocks, of four
||| blocks at least.
module Native.Runtime.Alloc.Config

import Native.Runtime.Bits

%default total

public export
record Config where
  constructor MkConfig
  ||| The smallest block, which every block's alignment is too: 4, 16 bytes.
  minShift : Bits64
  ||| The classes per doubling of size: 2, four.
  stepShift : Bits64
  ||| The largest block a slab holds: 16, 64 KiB.
  smallShift : Bits64
  ||| A granule, the smallest chunk, which the pagemap has an entry for: 14,
  ||| 16 KiB.
  granuleShift : Bits64
  ||| The largest chunk, which the arena takes from its region at a time,
  ||| and the largest block: 30, 1 GiB.
  maxChunkShift : Bits64
  ||| The region the arena reserves for its chunks: 36, 64 GiB of address
  ||| space, committed only as it is used.
  regionShift : Bits64
  ||| The empty slabs of a class kept for its next blocks before one is given
  ||| back, and the share of its slabs they may be (a quarter, as `quarter`
  ||| says).
  keepEmpty : Bits64

||| The configuration the runtime's allocator has.
export
defaultConfig : Config
defaultConfig = MkConfig 4 2 16 14 30 36 2

||| The index of the highest bit set in a word, 0 for 0 and 1: a binary
||| search, six steps.
export
highBit : Bits64 -> Bits64
highBit x = fst (step 1 (step 2 (step 4 (step 8 (step 16 (step 32 (0, x)))))))
  where
    step : (shift : Bits64) -> (Bits64, Bits64) -> (Bits64, Bits64)
    step s (n, y) = if y `shiftR` s /= 0 then (n + s, y `shiftR` s) else (n, y)

||| The least `k` such that `2^k >= n`.
export
ceilLog2 : Bits64 -> Bits64
ceilLog2 n = if n <= 1 then 0 else highBit (n - 1) + 1

||| The classes of the configuration's linear start: the steps of the
||| smallest block up to the first doubling.
steps : Config -> Bits64
steps c = 1 `shiftL` c.stepShift

||| The size class of a request of `bytes`, at most the largest block a slab
||| holds: in the linear start, the multiple of the smallest block it rounds
||| up to; past it, the doubling it is in and the step within it.
export
classOf : Config -> (bytes : Bits64) -> Bits64
classOf c bytes =
  let n = if bytes == 0 then 1 else bytes
      linear = steps c `shiftL` c.minShift
  in if n <= linear then ((n - 1) `shiftR` c.minShift)
     else let v = n - 1
              b = highBit v
          in steps c + (b - (c.minShift + c.stepShift)) * steps c
            + ((v `shiftR` (b - c.stepShift)) .&. (steps c - 1))

||| The bytes of a class's blocks: the largest request of the class.
export
classBytes : Config -> (cls : Bits64) -> Bits64
classBytes c k =
  if k < steps c then (k + 1) `shiftL` c.minShift
  else let e = (k - steps c) `shiftR` c.stepShift
           m = (k - steps c) .&. (steps c - 1)
       in ((steps c + 1 + m) `shiftL` c.minShift) `shiftL` e

||| The largest block a slab holds, and how many classes there are.
export
smallBytes : Config -> Bits64
smallBytes c = 1 `shiftL` c.smallShift

export
classCount : Config -> Bits64
classCount c = classOf c (smallBytes c) + 1

||| The order of a chunk: its granules' logarithm. A slab of a class is the
||| chunk of four of its blocks rounded up to a power of two, a granule at
||| least; a large block, the chunk it fits in.
export
slabOrder : Config -> (cls : Bits64) -> Bits64
slabOrder c k = let l = ceilLog2 (4 * classBytes c k) in if l <= c.granuleShift then 0 else l
  - c.granuleShift

export
chunkOrder : Config -> (bytes : Bits64) -> Bits64
chunkOrder c bytes = let l = ceilLog2 bytes in if l <= c.granuleShift then 0 else l - c.granuleShift

||| The order of the largest chunk.
export
maxOrder : Config -> Bits64
maxOrder c = c.maxChunkShift - c.granuleShift

||| The bytes of a chunk of the order.
export
chunkBytes : Config -> (order : Bits64) -> Bits64
chunkBytes c o = 1 `shiftL` (o + c.granuleShift)

||| Whether a class's empty slabs are too many to keep: more than
||| `keepEmpty`, and more than a quarter of its slabs.
export
quarter : Config -> (empty, slabs : Bits64) -> Bool
quarter c empty slabs = empty > c.keepEmpty && 4 * empty > slabs
