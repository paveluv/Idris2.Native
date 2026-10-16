||| The runtime's support tier: Idris's primitive types and the foreign
||| functions of the libraries Idris ships, implemented over the core
||| (`Native.Runtime`), as flat functions. The core knows objects by their
||| shapes; the support tier knows their types (`Native.Support.Obj`).
||| A program does not import it; the code generator loads it, by this
||| module, which imports the generic ones, and the string encoding's
||| module, which nothing generic imports.
module Native.Support

import public Native.Support.Foreign.Prelude.IO
import public Native.Support.Foreign.System

%default total
