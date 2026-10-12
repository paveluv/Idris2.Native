||| The encoder reports what it cannot encode faithfully: a field that does
||| not fit its bits, a displacement to a label included, and a label that
||| nothing defines. Each one in turn, after one that fits.
|||
||| An instruction field has a fixed width, such as a 32-bit displacement. A
||| value that does not fit would be truncated into a valid but different
||| instruction, so the encoder reports it instead, and the backend's
||| compilation fails rather than produce wrong code.
module Gen

import Compiler.Native.X86.Asm
import Compiler.Native.X86.Encode
import Data.Builder
import Data.SortedMap

check : String -> SortedMap Label Int -> List Instr -> IO ()
check what env is = do
  let (_, _, problems) = assembleWith env 0 is
  putStrLn (what ++ ": " ++ show problems)

main : IO ()
main = do
  check "fits" empty [MovRM RAX (MBase RBX 2147483647), AluI ADD RAX (-2147483648), Quad (-1)]
  check "displacement" empty [MovRM RAX (MBase RBX 2147483648)]
  check "immediate" empty [AluI ADD RAX 4294967296]
  check "store immediate" empty [MovMI (MBase RBX 0) 2147483648]
  check "64-bit immediate" empty [MovRI RAX 18446744073709551616]
  check "quad" empty [Quad (-9223372036854775809)]
  check "label too far" (fromList [(7, 4294967296)]) [Jmp 7]
  check "missing label" empty [Jmp 8]
