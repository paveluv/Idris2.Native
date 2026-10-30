||| Differential test of the x86-64 encoder against GNU as.
|||
||| Generates two instruction streams, the two groups of `Groups`: group A
||| in forms where GNU as's encoding is canonical, so bytes must match
||| exactly; group B in forms where as legitimately chooses a different
||| valid encoding, whose disassembly the run script compares instead.
|||
||| The encoder is the backend's assembler: it turns `Instr`, an Idris data
||| type of the x86-64 instructions the backend renders, into machine code.
||| GNU as is used here as a reference only; the product never runs it.
module Gen

import Data.Buffer
import Data.List
import Groups
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Data.Numbered
import System.File

writeBytes : String -> List Bits8 -> IO ()
writeBytes path bs = do
  let n = length bs
  Just buf <- newBuffer (cast n) | Nothing => putStrLn "buffer allocation failed"
  traverse_ (\(i, b) => setBits8 buf (cast i) b) (numbered bs)
  Right () <- writeBufferToFile path buf (cast n)
    | Left err => putStrLn ("write failed: " ++ show err)
  pure ()

emit : String -> List Instr -> IO ()
emit name is = do
  (code, missing) <- assemble 0 is
  let bytes = code <>> []
  writeBytes (name ++ ".bin") bytes
  ignore $
    writeFile (name ++ ".s")
      (".intel_syntax noprefix\n.text\n" ++ concat (map (\i => show i ++ "\n") is))
  putStrLn
    (name ++ ": " ++ show (length is) ++ " instructions, " ++ show (length bytes)
     ++ " bytes, missing labels: " ++ show (length missing))

main : IO ()
main = do
  emit "groupA" groupA
  emit "groupB" groupB
