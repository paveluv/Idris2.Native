||| Three binaries on the runtime seed alone: a result delivered
||| through HALT, the abort stub, and the grow-only allocator exercised
||| through two slow paths and one fast-path sequence.
module Gen

import Compiler.Native.X86.Asm
import Compiler.Native.Linkage
import Compiler.Native.Link
import Compiler.Native.ELF
import System.File

fix : Integer -> Integer
fix n = 2 * n + 1

-- 1. main returns fixnum 42 through k = HALT
exitProg : List Instr
exitProg = [Lbl (symLabel SymMain), MovRI RAX (fix 42), JmpM (MBase R12 0)]

-- 2. main hits the abort stub
unsupportedProg : List Instr
unsupportedProg = [Lbl (symLabel SymMain), Jmp (symLabel SymUnsupported)]

-- 3. A (3 words) via the slow path; B (8 MiB, larger than a window) via the
-- slow path, filling its window exactly; C through the inline fast path (lea,
-- cmp with r14, ja to the slow path), which must therefore take the slow
-- path; C points at A, and A's field is read back through C: 42 means every
-- window is mapped, bumped and intact.
slow, done : Label
slow = reservedLabels
done = reservedLabels + 1

allocProg : List Instr
allocProg =
  [ Lbl (symLabel SymMain)
  , MovRI RDI 24, Call (symLabel SymAllocSlow)
  , MovRI RDX 0x0000020000010001, MovMR (MBase RAX 0) RDX      -- HDR(CON, tag 1, nscan 2)
  , MovRI RDX (fix 42), MovMR (MBase RAX 8) RDX
  , MovMI (MBase RAX 16) 0
  , MovRR RBX RAX                                              -- A
  , MovRI RDI 0x800000, Call (symLabel SymAllocSlow)
  , MovRI RDX 7, MovMR (MBase RAX 0x7FFFF8) RDX                -- B's last word
  , Lea RCX (MBase R15 16), Alu CMP RCX R14, Jcc A slow        -- fast path for C (16 bytes)
  , MovRR RAX R15, MovRR R15 RCX, Jmp done
  , Lbl slow, MovRI RDI 16, Call (symLabel SymAllocSlow)
  , Lbl done
  , MovRI RDX 0x0000010000020001, MovMR (MBase RAX 0) RDX      -- HDR(CON, tag 2, nscan 1)
  , MovMR (MBase RAX 8) RBX                                    -- C.0 := A
  , MovRM RCX (MBase RAX 8), MovRM RAX (MBase RCX 8)           -- A.0 through C
  , JmpM (MBase R12 0) ]

emit : String -> List Instr -> IO ()
emit name prog = case link ({ val := FixnumTag1 } defaultEnc) prog of
  Left missing => putStrLn (name ++ ": unresolved labels " ++ show missing)
  Right image => do
    Right () <- writeImage name image
      | Left err => putStrLn (name ++ ": write failed: " ++ show err)
    putStrLn (name ++ ": " ++ show (length image) ++ " bytes")

main : IO ()
main = do
  emit "exit42" exitProg
  emit "unsupported" unsupportedProg
  emit "alloc" allocProg
