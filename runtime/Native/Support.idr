||| The runtime's support tier: Idris's own primitives and the values the
||| language has (strings, numbers, characters, buffers, the mutable cells,
||| pointers), implemented over the core (`Native.Runtime`), as flat
||| functions, with the foreign functions of the libraries Idris ships that
||| are about those values: a pointer's text read (`getString`), its test
||| for null, a buffer's bytes. The core knows objects by their shapes; the
||| support tier knows their types (`Native.Support.Obj`). What a C program
||| has from libc, files and the rest of the OS surface, is a system
||| library's (`Native.System`), not this tier's.
|||
||| Each of its foreign functions is the flat function of the foreign one's
||| name and type under `Native.Support.Foreign`, by the foreign one's
||| module path (`Data.Buffer.prim__newBuffer` by
||| `Native.Support.Foreign.Data.Buffer.prim__newBuffer`), which the code
||| generator binds it to where no system library implements it, so that
||| ordinary code calls it through the boundary, which converts its
||| arguments and its result as their types say.
|||
||| A program does not import it; the code generator loads it, by this
||| module, which imports the generic ones, and the string encoding's
||| module, which nothing generic imports. What it may hold is bounded: the
||| operations of Idris's primitive types, and those of the libraries'
||| foreign functions that are about the language's values, each listed by
||| the code generator's `dump-foreign` with how this backend implements it.
module Native.Support

import public Native.Support.Foreign.Data.Buffer
import public Native.Support.Foreign.Prelude.IO
import public Native.Support.Foreign.PrimIO

%default total
