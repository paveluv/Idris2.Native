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

import Data.SortedMap
import Native.Codegen.ELF
import Native.Codegen.LittleEndian
import Native.Codegen.Platform
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import System.File

main : IO ()
main = do
  let prog = [Lbl 0, MovRI RDI 42, MovRI RAX 231, Syscall]
  let (text, _, missing) = assemble textBase prog
  let lay = planLayout (byteCount text) 0 0
  Right () <- writeImage "exit42" (elfImage X86_64 lay (bytes (text <>> [])) (bytes []) 0 textBase)
    | Left err => putStrLn ("write failed: " ++ show err)
  putStrLn
    ("text bytes: " ++ show (byteCount text) ++ ", missing labels: " ++ show (length missing))
