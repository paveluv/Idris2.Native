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
import Native.Codegen.X86.LabelTable
import Sequences

-- A sequence's problems, as the link finds them: the labels' table made
-- for the labels below 16, of which the sequences' are, a label's address
-- held at its number; the text's labels put in it by the first pass
-- (`measure`), then the environment's, those outside the text
-- (`defineEnvironment`), then each instruction checked against them.
report : (String, SortedMap Label Int, List Instr) -> IO ()
report (what, env, is) = do
  labels <- labelTable 16
  measured <- measure labels 0 is
  outside <- defineEnvironment labels (SortedMap.toList env)
  problems <- check labels measured 0 is
  putStrLn (what ++ ": " ++ show (outside ++ problems))

main : IO ()
main = traverse_ report sequences
