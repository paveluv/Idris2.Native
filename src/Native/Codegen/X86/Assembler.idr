||| An assembler that encodes each instruction where it will run, as the
||| instructions come (`Assembler`), into a buffer of the text's bytes that
||| grows as it fills: the text is never a list. No instruction's size
||| depends on a label's value, since a reference to a label is always 32
||| bits, so each instruction's address is known when it is encoded, and
||| its alignment padding with it. A label the text defines is placed in
||| the labels' table as it comes; an instruction that refers to a label is
||| written with 0 where the displacement to it goes, and a fixup records
||| where that is, where the instruction ends, the label and the constant
||| added to its address, so that once every label has its address, the
||| data's, which wait for the text's size, among them, the fixups are
||| patched (`resolve`).
module Native.Codegen.X86.Assembler

import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Codegen.X86.InstrFormat
import Native.Codegen.X86.LabelTable

import Data.IORef
import Native.Data.ByteSink as Data
import Native.Data.GrowingBuffer as Data

%default total

||| What an assembler has made so far.
record Made where
  constructor MkMade
  ||| The text's bytes, those of its buffer filled.
  text : Data.GrowingBuffer
  labels : LabelTable
  ||| The fixups, four words each, those of its buffer filled: the offset in
  ||| the text of the 32-bit field, the offset of the end of the
  ||| instruction it is in, the label's number and the constant added to
  ||| its address.
  fixupTable : Data.GrowingBuffer
  ||| What is wrong, found as the text was encoded.
  problems : SnocList Encode.AsmProblem

||| An assembler of a text placed at `base`. Abstract: made by `assembler`
||| alone.
export
record Assembler where
  constructor MkAssembler
  base : Int
  made : IORef Made

||| The bytes of a fixup.
fixupBytes : Int
fixupBytes = 32

||| An assembler of a text placed at `base`, nothing encoded yet, with a
||| table of the labels below `labels` to begin with, which grows.
export
assembler : (base : Int) -> (labels : Nat) -> IO Assembler
assembler base n = do
  text <- Data.GrowingBuffer.growingBuffer 65536
  fixupTable <- Data.GrowingBuffer.growingBuffer 65536
  labels <- LabelTable.labelTable n
  made <- newIORef (MkMade text labels fixupTable [<])
  pure (MkAssembler base made)

||| The bytes the text takes so far.
export
size : Assembler -> IO Int
size a = map (Data.GrowingBuffer.used . (.text)) (readIORef a.made)

||| The labels' table, the text's labels in it, and the environment's once
||| it is resolved (`resolve`).
export
labels : Assembler -> IO LabelTable
labels a = map (.labels) (readIORef a.made)

||| The instructions encoded at the end of the text, in order. One that
||| cannot be held, past the most bytes a buffer can be made of, stops the
||| encoding with a problem (`TextTooLarge`).
export
encode : Assembler -> List Asm.Instr -> IO ()
encode a is = do
  m <- readIORef a.made
  Just s <- Data.GrowingBuffer.sink m.text
    | Nothing => writeIORef a.made ({ problems $= (:< Encode.TextTooLarge (Data.GrowingBuffer.used m.text)) } m)
  m' <- fromPrim
          (go s (Data.ByteSink.start s) m.text (Data.GrowingBuffer.used m.text) m.labels m.fixupTable
             (Data.GrowingBuffer.used m.fixupTable `div` fixupBytes) m.problems is)
  writeIORef a.made m'
  where
    -- The world passed by hand, so that the loop is a function of it: an
    -- `IO` loop with a clause that ends in a call Idris compiles as one
    -- that makes an action at each instruction. The loop's place in the
    -- sink over what is left of the text's buffer is a span of no bytes,
    -- which each instruction's writing ends at, and its offset `at`; a
    -- size and a fit are matched with their equations, as a `with` would,
    -- which the world, a linear name, keeps from being used here.
    go : (s : Data.ByteSink) -> Data.ByteSink.Span s 0 -> (text : Data.GrowingBuffer) -> (at : Int) ->
         LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) -> SnocList Encode.AsmProblem ->
         List Asm.Instr -> PrimIO Made
    sized : (s : Data.ByteSink) -> Data.ByteSink.Span s 0 -> (text : Data.GrowingBuffer) -> (at : Int) ->
            LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) -> SnocList Encode.AsmProblem ->
            Asm.Instr -> InstrFormat -> List Asm.Instr -> PrimIO Made
    checked : (s : Data.ByteSink) -> Data.ByteSink.Span s 0 -> (text : Data.GrowingBuffer) -> (at : Int) ->
              LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) -> SnocList Encode.AsmProblem ->
              Asm.Instr -> (k : Nat) -> (f : InstrFormat) -> (0 _ : InstrFormat.size f = k) ->
              List Asm.Instr -> PrimIO Made
    written : (s : Data.ByteSink) -> (place : Data.ByteSink.Span s 0) -> (text : Data.GrowingBuffer) ->
              (at : Int) -> LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) ->
              SnocList Encode.AsmProblem -> Asm.Instr -> (k : Nat) -> (f : InstrFormat) ->
              (0 _ : InstrFormat.size f = k) -> (fit : Bool) ->
              (0 _ : Data.ByteSink.fits s place k = fit) -> List Asm.Instr -> PrimIO Made
    regrown : (s : Data.ByteSink) -> (place : Data.ByteSink.Span s 0) -> (text : Data.GrowingBuffer) ->
              (at : Int) -> LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) ->
              SnocList Encode.AsmProblem -> Asm.Instr -> (k : Nat) -> (f : InstrFormat) ->
              (0 _ : InstrFormat.size f = k) -> (fit : Bool) ->
              (0 _ : Data.ByteSink.fits s place k = fit) -> List Asm.Instr -> PrimIO Made
    wrote : (s : Data.ByteSink) -> (place : Data.ByteSink.Span s 0) -> (text : Data.GrowingBuffer) ->
            (at : Int) -> LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) ->
            SnocList Encode.AsmProblem -> Asm.Instr -> (k : Nat) -> (f : InstrFormat) ->
            (0 _ : InstrFormat.size f = k) -> (0 _ : Data.ByteSink.fits s place k = True) ->
            List Asm.Instr -> PrimIO Made
    noted : (s : Data.ByteSink) -> Data.ByteSink.Span s 0 -> (text : Data.GrowingBuffer) -> (at : Int) ->
            LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) -> SnocList Encode.AsmProblem ->
            Asm.Instr -> (start : Int) -> InstrFormat -> List Asm.Instr -> PrimIO Made
    recorded : (s : Data.ByteSink) -> Data.ByteSink.Span s 0 -> (text : Data.GrowingBuffer) -> (at : Int) ->
               LabelTable -> (fixupTable : Data.GrowingBuffer) -> (fixups : Int) -> SnocList Encode.AsmProblem ->
               (field : Int) -> Asm.Label -> (constant : Int) -> List Asm.Instr -> PrimIO Made

    -- what the encoding has made, the text filled to `at` and the
    -- fixups' table to its fixups
    made : Data.GrowingBuffer -> (at : Int) -> LabelTable -> Data.GrowingBuffer -> (fixups : Int) ->
           SnocList Encode.AsmProblem -> Made
    made text at labels fixupTable fixups problems =
      MkMade (Data.GrowingBuffer.filledTo text at) labels (Data.GrowingBuffer.filledTo fixupTable (fixupBytes * fixups)) problems

    go s place text at labels fixupTable fixups problems [] w =
      MkIORes (made text at labels fixupTable fixups problems) w
    go s place text at labels fixupTable fixups problems (i :: rest) w = case i of
      Asm.Lbl l => case toPrim (LabelTable.holding labels l) w of
        MkIORes (Just t) w1 => case toPrim (LabelTable.define t l (a.base + at)) w1 of
          MkIORes _ w2 => go s place text at t fixupTable fixups problems rest w2
        MkIORes Nothing w1 =>
          go s place text at labels fixupTable fixups (problems :< Encode.LabelPastBound l) rest w1
      Asm.Comment _ => go s place text at labels fixupTable fixups problems rest w
      _ =>
        sized s place text at labels fixupTable fixups
          (if Encode.fieldsFit i then problems else problems :< Encode.DoesNotFit i) i
          (Encode.instrFormat (a.base + at) 0 i) rest w

    -- the instruction's size read once, as an argument, with its equation
    sized s place text at labels fixupTable fixups problems i f rest w =
      checked s place text at labels fixupTable fixups problems i (InstrFormat.size f) f Refl
        rest w

    checked s place text at labels fixupTable fixups problems i k f same rest w =
      written s place text at labels fixupTable fixups problems i k f same
        (Data.ByteSink.fits s place k) Refl rest w

    -- the parts written at the place, if they fit before the buffer's end;
    -- else the buffer grown to hold them (`grownTo`), and the parts written
    -- at the same offset of the larger one, through a sink over its room
    written s place text at labels fixupTable fixups problems i k f same True fit rest w =
      wrote s place text at labels fixupTable fixups problems i k f same fit rest w
    written s place text at labels fixupTable fixups problems i k f same False _ rest w =
      case toPrim (Data.GrowingBuffer.grownTo text (at + cast k)) w of
        MkIORes Nothing w1 =>
          MkIORes (made text at labels fixupTable fixups (problems :< Encode.TextTooLarge at)) w1
        MkIORes (Just t) w1 => case toPrim (Data.GrowingBuffer.sink (Data.GrowingBuffer.filledTo t at)) w1 of
          MkIORes Nothing w2 =>
            MkIORes (made t at labels fixupTable fixups (problems :< Encode.TextTooLarge at)) w2
          MkIORes (Just s') w2 =>
            regrown s' (Data.ByteSink.start s') t at labels fixupTable fixups problems i k f same
              (Data.ByteSink.fits s' (Data.ByteSink.start s') k) Refl rest w2

    -- after growing, the parts fit or the text cannot be held
    regrown s place text at labels fixupTable fixups problems i k f same True fit rest w =
      wrote s place text at labels fixupTable fixups problems i k f same fit rest w
    regrown s place text at labels fixupTable fixups problems i k f same False _ rest w =
      MkIORes (made text at labels fixupTable fixups (problems :< Encode.TextTooLarge at)) w

    wrote s place text at labels fixupTable fixups problems i k f same fit rest w =
      case toPrim (InstrFormat.write s f (rewrite same in Data.ByteSink.span s place k fit)) w of
        MkIORes end w1 =>
          noted s end text (at + cast k) labels fixupTable fixups problems i at f rest w1

    -- A fixup recorded for an instruction that refers to a label: its
    -- field after the bytes before its displacement (`dispAt`), as
    -- `instrLabel` says. A label past the most a table holds can have no
    -- address, and is missing at once.
    noted s place text at labels fixupTable fixups problems i start f rest w =
      case Encode.instrLabel i of
        Nothing => go s place text at labels fixupTable fixups problems rest w
        Just (l, d) =>
          if natToInteger l >= LabelTable.mostLabels
            then go s place text at labels fixupTable fixups (problems :< Encode.MissingLabel l) rest w
            else recorded s place text at labels fixupTable fixups problems
                   (start + cast (InstrFormat.dispAt f)) l d rest w

    -- the fixup's four words written, the table grown first to hold them
    -- if it has no room for them (`grownTo`)
    recorded s place text at labels fixupTable fixups problems field l d rest w =
      let past = fixupBytes * (fixups + 1) in
      if past <= Data.GrowingBuffer.capacity fixupTable
        then case toPrim (four fixupTable) w of
          MkIORes () w1 => go s place text at labels fixupTable (fixups + 1) problems rest w1
        else case toPrim (Data.GrowingBuffer.grownTo fixupTable past) w of
          MkIORes (Just t) w1 => case toPrim (four t) w1 of
            MkIORes () w2 => go s place text at labels t (fixups + 1) problems rest w2
          MkIORes Nothing w1 =>
            MkIORes (made text at labels fixupTable fixups (problems :< Encode.TextTooLarge at)) w1
      where
        four : Data.GrowingBuffer -> IO ()
        four t = do
          let o = fixupBytes * fixups
          Data.GrowingBuffer.setInt t o field
          Data.GrowingBuffer.setInt t (o + 8) at
          Data.GrowingBuffer.setInt t (o + 16) (cast l)
          Data.GrowingBuffer.setInt t (o + 24) d

||| The environment's labels defined, unless the text defines them, of a
||| label given twice the first, then every fixup patched with the
||| displacement to its label (`labelDisplacement`): what is wrong, the
||| problems found as the text was encoded first, then a label of the
||| environment with no place, then, in the text's order, each label with
||| no address and each displacement that does not fit its 32 bits.
export
resolve : Assembler -> (env : List (Asm.Label, Int)) -> IO (List Encode.AsmProblem)
resolve a env = do
  m <- readIORef a.made
  (labels, outside) <- environment m.labels [<] env
  writeIORef a.made ({ labels := labels } m)
  found <- fromPrim
             (patched m.text labels m.fixupTable (cast (Data.GrowingBuffer.used m.fixupTable `div` fixupBytes)) 0 [<])
  pure ((m.problems <>> []) ++ (outside <>> []) ++ found)
  where
    environment : LabelTable -> SnocList Encode.AsmProblem -> List (Asm.Label, Int) ->
                  IO (LabelTable, SnocList Encode.AsmProblem)
    environment t past [] = pure (t, past)
    environment t past ((l, address) :: rest) = do
      Just t' <- LabelTable.holding t l
        | Nothing => environment t (past :< Encode.LabelPastBound l) rest
      _ <- LabelTable.defineNew t' l address
      environment t' past rest

    -- the displacement written into the text, if its field lies in what is
    -- filled
    patch : Data.GrowingBuffer -> (field, displacement : Int) -> IO ()
    patch text field d =
      if field + 4 <= Data.GrowingBuffer.used text then Data.GrowingBuffer.setBits32 text field (cast d) else pure ()

    -- Each fixup in turn, `left` of them from the `i`th, the world passed
    -- by hand: in an `IO` loop, the match on `S` binds the count's
    -- predecessor before the step, and Idris compiles the loop as one
    -- that makes an action at each step.
    patched : (text : Data.GrowingBuffer) -> LabelTable -> (fixupTable : Data.GrowingBuffer) ->
              (left : Nat) -> (i : Int) -> SnocList Encode.AsmProblem ->
              PrimIO (List Encode.AsmProblem)
    patched text labels fixupTable Z i found w = MkIORes (found <>> []) w
    patched text labels fixupTable (S left) i found w =
      let o = fixupBytes * i in
      case toPrim (Data.GrowingBuffer.getInt fixupTable o) w of
        MkIORes field w1 => case toPrim (Data.GrowingBuffer.getInt fixupTable (o + 8)) w1 of
          MkIORes end w2 => case toPrim (Data.GrowingBuffer.getInt fixupTable (o + 16)) w2 of
            MkIORes number w3 => case toPrim (Data.GrowingBuffer.getInt fixupTable (o + 24)) w3 of
              MkIORes d w4 =>
                let l = the Asm.Label (cast number) in
                case toPrim (LabelTable.address labels l) w4 of
                  MkIORes Nothing w5 =>
                    patched text labels fixupTable left (i + 1) (found :< Encode.MissingLabel l) w5
                  MkIORes (Just address) w5 =>
                    -- from the end of the instruction, an instruction of no
                    -- bytes there
                    let rel = Encode.labelDisplacement (a.base + end) 0 address d in
                    if Encode.fitsInt32 (cast rel)
                      then case toPrim (patch text field rel) w5 of
                        MkIORes () w6 => patched text labels fixupTable left (i + 1) found w6
                      else
                        patched text labels fixupTable left (i + 1)
                          (found :< Encode.LabelTooFar l (a.base + end)) w5

||| The text's bytes written at the sink's next offset, if they fit before
||| its end, with one copy.
export
put : Assembler -> Data.ByteSink -> IO (Maybe Data.ByteSink)
put a s = do
  m <- readIORef a.made
  Data.GrowingBuffer.put s m.text
