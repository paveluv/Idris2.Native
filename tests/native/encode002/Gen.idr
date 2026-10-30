||| The encoder reports what it cannot encode faithfully: a field that does
||| not fit its bits, a displacement to a label too far for its 32 bits,
||| and a label that nothing defines. Each one in turn, after one that fits
||| (`Sequences`); last, a label both the text and the labels outside it
||| define, the text's taken.
|||
||| An instruction field has a fixed width, such as a 32-bit displacement. A
||| value that does not fit would be truncated into a valid but different
||| instruction, so the encoder reports it instead, and the backend's
||| compilation fails rather than produce wrong code.
module Gen

import Data.SortedMap
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Assembler
import Native.Codegen.X86.Encode
import Sequences

-- A sequence's problems, as the link finds them: the sequence encoded by
-- an assembler, its labels' table made for the labels below 16 to begin
-- with, of which the sequences' are; then the environment's labels, those
-- outside the text, defined and every label reference fixed up
-- (`resolve`), which finds what is wrong with the fields that refer to
-- labels.
report : (String, SortedMap Label Int, List Instr) -> IO ()
report (what, env, is) = do
  asm <- assembler 0 16
  encode asm is
  problems <- resolve asm (SortedMap.toList env)
  putStrLn (what ++ ": " ++ show problems)

main : IO ()
main = traverse_ report sequences
