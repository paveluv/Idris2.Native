||| A binary produced with no assembler and no linker in the path: encoder
||| bytes wrapped in a static ELF64 image. The program is
||| `_start: exit_group(42)`.
|||
||| Every executable the backend makes is built this way: its own encoder
||| turns instructions, an Idris data type, into bytes, and its own writer
||| lays them out as an ELF file that Linux loads at fixed addresses. No
||| assembler, linker or C library takes part. 231 is the system call that
||| ends the process with the status in rdi.
module Gen

import Compiler.Native.ELF
import Compiler.Native.Platform
import Compiler.Native.X86.Asm
import Compiler.Native.X86.Encode
import Data.Builder
import Data.SortedMap
import System.File

main : IO ()
main = do
  let prog = [Lbl 0, MovRI RDI 42, MovRI RAX 231, Syscall]
  let (text, _, missing) = assemble textBase prog
  let lay = planLayout (cast (size text)) 0 0
  Right () <- writeImage "exit42" (elfImage X86_64 lay text neutral 0 textBase)
    | Left err => putStrLn ("write failed: " ++ show err)
  putStrLn ("text bytes: " ++ show (size text) ++ ", missing labels: " ++ show (length missing))
