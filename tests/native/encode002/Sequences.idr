||| The sequences the encoder's reports are tested on (`Gen`), which the
||| test of the encoder's readings (`tests/native/encode003`) uses too:
||| one that fits, then each thing the encoder cannot encode faithfully in
||| turn, a field that does not fit its bits, a displacement to a label
||| too far for its 32 bits, and a label that nothing defines; last, a
||| label that both the text and the labels outside it define.
module Sequences

import Data.SortedMap
import Native.Codegen.X86.Asm

||| Each sequence with what it shows and the labels defined outside it, at
||| their addresses.
export
sequences : List (String, SortedMap Label Int, List Instr)
sequences =
  [ ("fits", empty, [MovRM RAX (MBase RBX 2147483647), AluI ADD RAX (-2147483648), Quad (-1)])
  , ("displacement", empty, [MovRM RAX (MBase RBX 2147483648)])
  , ("immediate", empty, [AluI ADD RAX 4294967296])
  , ("store immediate", empty, [MovMI (MBase RBX 0) 2147483648])
  , ("64-bit immediate", empty, [MovRI RAX 18446744073709551616])
  , ("quad", empty, [Quad (-9223372036854775809)])
  , ("label too far", fromList [(7, 4294967296)], [Jmp 7])
  , ("missing label", empty, [Jmp 8])
  -- Label 1 is the text's `Lbl 1`, just past the jump, which then jumps
  -- by 0, and it is also outside the text, 2^32 bytes past its start, too
  -- far for the jump's 32 bits. The text's label is the one taken, since
  -- an environment's label is defined only where the text defines none
  -- (`resolve`), so the jump fits; the other would not, as "label too far"
  -- shows.
  , ("text labels first", fromList [(1, 4294967296)], [Jmp 1, Lbl 1]) ]
