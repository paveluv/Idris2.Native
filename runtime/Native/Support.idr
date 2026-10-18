||| The runtime's support tier: Idris's primitive types and the foreign
||| functions of the libraries Idris ships, implemented over the core
||| (`Native.Runtime`), as flat functions. The core knows objects by their
||| shapes; the support tier knows their types (`Native.Support.Obj`).
||| A program does not import it; the code generator loads it, by this
||| module, which imports the generic ones, and the string encoding's
||| module, which nothing generic imports.
|||
||| What it may hold is bounded: the operations of Idris's primitive types,
||| and the `%foreign` and `%extern` functions the libraries Idris ships
||| declare, which the code generator's `dump-foreign` lists, each with how
||| this backend implements it. It grows by that list and never past it.
||| Those of its functions tied to no syntax or literal (files, buffers,
||| clocks, the network) may later move to a standard library written as any
||| library is; those tied to literals (strings, integers, doubles,
||| characters, and the casts among them) stay, as the code generator lays
||| their literals out.
module Native.Support

import public Native.Support.Foreign.Prelude.IO
import public Native.Support.Foreign.PrimIO
import public Native.Support.Foreign.System
import public Native.Support.Foreign.System.FFI

%default total
