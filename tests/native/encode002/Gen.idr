||| The encoder reports what it cannot encode faithfully: a field that does
||| not fit its bits, a displacement to a label included, and a label that
||| nothing defines. Each one in turn, after one that fits (`Sequences`);
||| last, a label both the text and the labels outside it define, the
||| text's taken.
|||
||| An instruction field has a fixed width, such as a 32-bit displacement. A
||| value that does not fit would be truncated into a valid but different
||| instruction, so the encoder reports it instead, and the backend's
||| compilation fails rather than produce wrong code.
module Gen

import Data.SortedMap
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Sequences

check : (String, SortedMap Label Int, List Instr) -> IO ()
check (what, env, is) = do
  let measured = measure 0 is
      problems = check (labelsWith env measured) measured 0 is
  putStrLn (what ++ ": " ++ show problems)

main : IO ()
main = traverse_ check sequences
