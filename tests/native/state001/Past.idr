||| A word past the area: `count 32` asks for `32 < 32 = True`, which is
||| false, so it does not typecheck, and a state that grew past its area is
||| refused where the runtime is built, not found writing past the image.
module Past

import Native.Runtime.State

%default total

pastWord : State Bits64
pastWord = count 32
