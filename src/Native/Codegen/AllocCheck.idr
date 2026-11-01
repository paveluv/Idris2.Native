||| An independent check of what register allocation made (`check`): the
||| located IR of every function, read alone, without the allocator, which
||| it never imports.
|||
||| A register is a location; the check holds the IR to what the rendering
||| and the collector rely on of locations:
|||
||| * **One kind of value a slot.** A slot holds values the collector sees,
|||   under any of their types, since a `Val` and a pointer to the object
|||   are the same word, or raw words only, as a byte address and its word,
|||   whose retyping has no code. A slot that held a value the collector
|||   must see under one name and a raw word under another would hide one
|||   from the collector, or show it a word that is not a value.
||| * **Defined before used.** On every path from the function's entry,
|||   or from a resume block, a register is written before it is read: by an
|||   instruction, as a parameter of the function, or as a resume block's
|||   parameter, which the continuation's fields give back. A block is
|||   entered with what every block that jumps or branches to it defines on
|||   the way, a must analysis to its fixed point; a block nothing reaches
|||   is not checked.
||| * **Everything live kept.** Where a collection can start, an
|||   allocation or a direct call that may collect, the `live` list names
|||   every GC-visible register read after it, the allocation's own operands
|||   included, which the object is initialised from afterwards: what it
|||   leaves out the collector would not forward. And it names only
|||   registers defined there. A non-tail call's continuation holds what
|||   its resume block reads: a resume block's parameters are the
|||   continuation's registers and the result, and the block reads nothing
|||   else from before it, since no register survives the call. What is read
|||   after a point is a may analysis, backward to its fixed point.
|||
||| * **No register across what overwrites it.** A value may be in one of the
|||   target's allocatable registers, named by its index among those of its
|||   class in the target's description; an index past them is rejected.
|||   No register survives the allocation slow path, which keeps the slots,
|||   nor a direct call, whose callee may write any: none is live where a
|||   collection can start or across a direct call.
|||
||| What this does not check is that a register holds the value the term IR
||| means at its use: the located IR alone does not say which value that
||| is. Each rejection names the function and the block.
module Native.Codegen.AllocCheck

import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.LocatedIR.Block as LocatedIR
import Native.Codegen.LocatedIR.Cont as LocatedIR
import Native.Codegen.LocatedIR.Function as LocatedIR
import Native.Codegen.LocatedIR.Instr as LocatedIR
import Native.Codegen.LocatedIR.Label as LocatedIR
import Native.Codegen.LocatedIR.Location as LocatedIR
import Native.Codegen.LocatedIR.Mem as LocatedIR
import Native.Codegen.LocatedIR.Opnd as LocatedIR
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Terminator as LocatedIR
import Native.Codegen.RegDesc
import Native.Codegen.Target

import Core.Name
import Data.Bits
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.Zippable
import Native.Rep
import Native.Types.Enc as Types

%default total

------------------------------------------------------------------------------
-- What each instruction and terminator reads, writes and keeps

------------------------------------------------------------------------------
-- The check

||| Slots as a set: bit n stands for slot n.
Slots : Type
Slots = Integer

||| What a block reads before it writes it, and what it writes, read once:
||| from these and what is read after it, what is read before it. A block
||| that may leave through an overflow is walked instead, since what its
||| overflow block reads joins in the middle.
record Summary (enc : Types.Enc) where
  constructor MkSummary
  reads : Slots
  writes : Slots
  ||| The overflow blocks the block may leave to, each with what the block
  ||| has written by then.
  sides : List (LocatedIR.Label, Slots)
  ||| Each instruction, with what it reads and what it writes.
  steps : List (LocatedIR.Instr enc, Slots, Slots)
  ||| What the block reads after each instruction before it writes it, the
  ||| terminator included: all that is read after the instruction when the
  ||| block jumps and branches nowhere.
  afters : List Slots
  ||| The slots the live lists name before the block writes them.
  listed : Slots
  ||| The slots the block names under a GC-visible type, and under a raw one.
  gcNamed : Slots
  rawNamed : Slots
  ||| The registers the block names past the target's description.
  undescribed : List (LocatedIR.Location enc)

||| One function's blocks by label, with each block's predecessors, summary,
||| and an order to compute in.
record Shape (enc : Types.Enc) where
  constructor MkShape
  blocks : SortedMap LocatedIR.Label (LocatedIR.Block enc, Summary enc)
  ||| The blocks that jump, branch or overflow to each block.
  preds : SortedMap LocatedIR.Label (List LocatedIR.Label)
  ||| The resume blocks.
  resumes : SortedSet LocatedIR.Label
  ||| The blocks the entry and the resume blocks reach, each after every
  ||| block it reaches but those back along a loop (a postorder).
  post : List LocatedIR.Label
  ||| Whether a block reaches one before it in that order: a loop.
  loops : Bool

||| Every function of the program checked: the first rejection, if any.
export covering
check : LocatedIR.Program enc -> Either String ()
check p = traverse_ checkFunction p.functions
  where
    ||| The target's registers, which locations are numbered by.
    rd : RegDesc
    rd = p.target.allocatable

    ||| A location's number, for sets of them.
    number : LocatedIR.Location enc -> Nat
    number = LocatedIR.Location.key rd

    ||| Whether the location is a slot, or a register the description has an
    ||| index for in its class.
    described : LocatedIR.Location enc -> Bool
    described (LocatedIR.Location.Slot _ _) = True
    described (LocatedIR.Location.Register i t) = case IRCommon.Ty.class t of
      Rep.WordClass => i < rd.wordCount
      Rep.FloatClass => i < rd.floatCount

    ||| The numbers of the registers.
    registers : Slots
    registers = bit (rd.wordCount + rd.floatCount) - 1

    ||| A direct call, after which a callee has written any register.
    directCall : LocatedIR.Instr enc -> Bool
    directCall (LocatedIR.Instr.DirectCall _ _ _ _ _) = True
    directCall _ = False

    ||| What a location's number names, for a rejection.
    named : Nat -> String
    named k =
      let w = rd.wordCount
          f = rd.floatCount
      in if k < w then "word register " ++ show k
         else if k < w + f then "floating-point register " ++ show (minus k w)
         else "slot " ++ show (minus k (w + f))

    ||| One function checked.
    covering
    checkFunction : LocatedIR.Function enc -> Either String ()
    checkFunction f = do
      let sh = shape f
          sums = map snd (values sh.blocks)
          gcs = foldl (\s, sm => s .|. sm.gcNamed)
                  (slots (filter (IRCommon.Ty.gcVisible . LocatedIR.Location.ty) f.params)) sums
          raws = foldl (\s, sm => s .|. sm.rawNamed)
                   (slots (filter (not . IRCommon.Ty.gcVisible . LocatedIR.Location.ty) f.params)) sums
          both = gcs .&. raws
      case concatMap (.undescribed) sums of
        (r :: _) => reject f f.entry (show r ++ " is a register the target does not describe")
        [] => Right ()
      when (both /= 0) $ do
        let n = lowest both
            names : (LocatedIR.Label, (LocatedIR.Block enc, Summary enc)) -> Bool
            names (_, (_, sm)) = testBit (sm.gcNamed .|. sm.rawNamed) n
        reject f (fromMaybe f.entry (map fst (find names (SortedMap.toList sh.blocks))))
          (named n ++ " holds a value the collector sees and a raw word")
      let live = liveIn sh
          defined = definedIn f sh
      traverse_
        (\(l, bsm) => maybe (Right ()) (\d => checkBlock f sh gcs live d bsm) (lookup l defined))
        (SortedMap.toList sh.blocks)
      where
        ||| The registers of the operands.
        opnds : List (LocatedIR.Opnd enc) -> List (LocatedIR.Location enc)
        opnds os = LocatedIR.Opnd.opsRegs os []

        ||| What an instruction reads: its operands, not the registers its `live`
        ||| list keeps.
        uses : LocatedIR.Instr enc -> List (LocatedIR.Location enc)
        uses i = case i of
          LocatedIR.Instr.Mul128 _ _ x y => opnds [x, y]
          LocatedIR.Instr.Div128 _ _ h l x => opnds [h, l, x]
          LocatedIR.Instr.Store _ m x => x :: memRegs m
          LocatedIR.Instr.StoreN _ m x => x :: memRegs m
          LocatedIR.Instr.Load _ _ m => memRegs m
          LocatedIR.Instr.LoadN _ _ _ m => memRegs m
          LocatedIR.Instr.AllocObj _ _ fs _ => opnds fs
          LocatedIR.Instr.AllocSized _ _ count fill _ => count
            :: maybe [] LocatedIR.Opnd.opRegs fill
          LocatedIR.Instr.DirectCall _ args _ _ _ => opnds args
          LocatedIR.Instr.SetPinned _ x => LocatedIR.Opnd.opRegs x
          LocatedIR.Instr.SystemCall _ args => opnds args
          LocatedIR.Instr.Loc _ => []
          LocatedIR.Instr.Comment _ => []
          _ => drop 1 (LocatedIR.Instr.instrRegs i)
          where
            ||| The registers a memory operand reads.
            memRegs : LocatedIR.Mem enc -> List (LocatedIR.Location enc)
            memRegs m = m.base :: maybe [] (\r => [r]) m.index

        ||| The block an instruction may leave to, an overflow's.
        side : LocatedIR.Instr enc -> Maybe LocatedIR.Label
        side (LocatedIR.Instr.ArithOv _ _ _ _ l) = Just l
        side (LocatedIR.Instr.TagOv _ _ l) = Just l
        side _ = Nothing

        ||| What a terminator reads: a non-tail call's continuation reads its
        ||| registers, to keep them.
        termUses : LocatedIR.Terminator enc -> List (LocatedIR.Location enc)
        termUses t = case t of
          LocatedIR.Terminator.Jump _ => []
          LocatedIR.Terminator.IfFixnums rs _ _ => rs
          LocatedIR.Terminator.Branch _ x y _ _ => opnds [x, y]
          LocatedIR.Terminator.Switch r _ _ => [r]
          LocatedIR.Terminator.Call _ xs c => opnds xs ++ c.live
          LocatedIR.Terminator.TailCall _ xs => opnds xs
          LocatedIR.Terminator.Apply f x c => f :: x :: c.live
          LocatedIR.Terminator.TailApply f x => [f, x]
          LocatedIR.Terminator.Return x => LocatedIR.Opnd.opRegs x
          LocatedIR.Terminator.Enter f xs => f :: opnds xs
          LocatedIR.Terminator.Ret xs => opnds xs
          LocatedIR.Terminator.Crash _ => []
          LocatedIR.Terminator.Unsupported _ => []

        ||| The blocks a terminator jumps or branches to. A non-tail call's resume
        ||| block is entered from the continuation, not from the call.
        succs : LocatedIR.Terminator enc -> List LocatedIR.Label
        succs t = case t of
          LocatedIR.Terminator.Jump l => [l]
          LocatedIR.Terminator.IfFixnums _ y n => [y, n]
          LocatedIR.Terminator.Branch _ _ _ y n => [y, n]
          LocatedIR.Terminator.Switch _ cs d => map snd cs ++ [d]
          _ => []

        ||| The continuation a non-tail call resumes at.
        continuation : LocatedIR.Terminator enc -> Maybe (LocatedIR.Cont enc)
        continuation (LocatedIR.Terminator.Call _ _ c) = Just c
        continuation (LocatedIR.Terminator.Apply _ _ c) = Just c
        continuation _ = Nothing

        slots : List (LocatedIR.Location enc) -> Slots
        slots = foldl (\s, r => s .|. bit (number r)) 0

        ||| The slots of the first set that are not in the second.
        minus : Slots -> Slots -> Slots
        minus a b = a .&. xor b (-1)

        shape : LocatedIR.Function enc -> Shape enc
        shape f =
          let bs = fromList (map (\b => (b.label, (b, summary b))) f.blocks)
              edges = concatMap (\b => map (\s => (s, b.label)) (nexts b)) f.blocks
              ps = foldl (\m, (s, p) => insert s (p :: fromMaybe [] (lookup s m)) m)
                     (the (SortedMap LocatedIR.Label (List LocatedIR.Label)) empty) edges
              rs = fromList (mapMaybe (\b => map (.resume) (continuation b.term)) f.blocks)
              (post, loops) = walk bs (f.entry :: SortedSet.toList rs)
          in MkShape bs ps rs post loops
          where
            ||| The blocks a block jumps, branches or overflows to.
            nexts : LocatedIR.Block enc -> List LocatedIR.Label
            nexts b = succs b.term ++ mapMaybe side b.body

            -- a depth-first walk, a block done once every block it reaches is: an
            -- explicit stack of blocks, each with the successors left to visit;
            -- reaching a block on the stack is reaching back along a loop
            walk : SortedMap LocatedIR.Label (LocatedIR.Block enc, Summary enc) ->
                   List LocatedIR.Label ->
                   (List LocatedIR.Label, Bool)
            walk bs roots = go (S (length (SortedMap.toList bs)) * 4) roots [] empty empty [<] False
              where
                go : Nat -> List LocatedIR.Label -> List (LocatedIR.Label, List LocatedIR.Label) ->
                     SortedSet LocatedIR.Label -> SortedSet LocatedIR.Label ->
                     SnocList LocatedIR.Label -> Bool -> (List LocatedIR.Label, Bool)
                go Z _ _ _ _ acc back = (acc <>> [], back)
                go (S n) roots ((l, []) :: stack) seen onStack acc back =
                  go n roots stack seen (delete l onStack) (acc :< l) back
                go (S n) roots ((l, s :: ss) :: stack) seen onStack acc back =
                  if contains s onStack then go n roots ((l, ss) :: stack) seen onStack acc True
                  else if contains s seen then go n roots ((l, ss) :: stack) seen onStack acc back
                  else case lookup s bs of
                    Nothing => go n roots ((l, ss) :: stack) seen onStack acc back
                    Just (b, _) => go n roots ((s, nexts b) :: (l, ss) :: stack) (insert s seen)
                                     (insert s onStack) acc back
                go (S n) (r :: roots) [] seen onStack acc back =
                  if contains r seen then go n roots [] seen onStack acc back
                  else case lookup r bs of
                    Nothing => go n roots [] seen onStack acc back
                    Just (b, _) =>
                      go n roots [(r, nexts b)] (insert r seen) (insert r onStack) acc back
                go (S _) [] [] _ _ acc back = (acc <>> [], back)

            summary : LocatedIR.Block enc -> Summary enc
            summary b =
              let steps = map (\i => (i, slots (uses i), slots (defs i))) b.body
                  (r, w, as) =
                    foldr (\(_, u, d), (r', w', as') => (minus r' d .|. u, w' .|. d, r' :: as'))
                                     (slots (termUses b.term), 0, []) steps
                  (sds, ls) = forward 0 steps
                  named =
                    foldl (\acc,
                           i => foldl kind acc (defs i ++ uses i ++ fromMaybe [] (listedIn i)))
                            (foldl kind (0, 0, []) (b.params ++ termUses b.term)) b.body
                  (gcNamed, rawNamed, undescribed) = named
              in MkSummary (minus r (slots b.params)) (w .|. slots b.params) sds steps as ls
                   gcNamed rawNamed undescribed
              where
                -- the registers a `live` list names, whether or not a
                -- collection can start there
                listedIn : LocatedIR.Instr enc -> Maybe (List (LocatedIR.Location enc))
                listedIn i = case i of
                  LocatedIR.Instr.AllocObj _ _ _ live => Just live
                  LocatedIR.Instr.AllocSized _ _ _ _ live => Just live
                  LocatedIR.Instr.DirectCall _ _ _ _ live => Just live
                  _ => Nothing

                -- the `live` list of an instruction where a collection can start
                collectingHere : LocatedIR.Instr enc -> Maybe (List (LocatedIR.Location enc))
                collectingHere (LocatedIR.Instr.DirectCall _ _ _ False _) = Nothing
                collectingHere i = listedIn i

                -- the overflows, each with what the block has written by then,
                -- and what the live lists name before the block writes it
                forward : Slots -> List (LocatedIR.Instr enc, Slots, Slots) ->
                          (List (LocatedIR.Label, Slots), Slots)
                forward _ [] = ([], 0)
                forward w ((i, _, d) :: is) =
                  let (rest, ls) = forward (w .|. d) is
                  in (maybe rest (\l => (l, w) :: rest) (side i),
                      maybe ls (\l => ls .|. minus (slots l) w) (collectingHere i))

                -- the slots by kind, and the registers the description has
                -- no index for
                kind : (Slots, Slots, List (LocatedIR.Location enc)) -> LocatedIR.Location enc ->
                       (Slots, Slots, List (LocatedIR.Location enc))
                kind (gc, raw, out) r =
                  if not (described r) then (gc, raw, r :: out)
                  else if IRCommon.Ty.gcVisible (LocatedIR.Location.ty r)
                    then (gc .|. bit (number r), raw, out)
                  else (gc, raw .|. bit (number r), out)

                ||| What an instruction writes.
                defs : LocatedIR.Instr enc -> List (LocatedIR.Location enc)
                defs i = case i of
                  LocatedIR.Instr.Mul128 h l _ _ => [h, l]
                  LocatedIR.Instr.Div128 q r _ _ _ => [q, r]
                  LocatedIR.Instr.Store _ _ _ => []
                  LocatedIR.Instr.StoreN _ _ _ => []
                  LocatedIR.Instr.DirectCall _ _ ds _ _ => ds
                  LocatedIR.Instr.SetPinned _ _ => []
                  LocatedIR.Instr.Loc _ => []
                  LocatedIR.Instr.Comment _ => []
                  _ => take 1 (LocatedIR.Instr.instrRegs i)

        ||| The lowest slot of a set that is not empty.
        lowest : Slots -> Nat
        lowest s = go 0 (S (cast {to = Nat} (integerLog2 s)))
          where
            integerLog2 : Integer -> Integer
            -- lint: allow trust-escape: x is at least 2 here, so its half is smaller and positive
            integerLog2 x = if x <= 1 then 0 else 1 + integerLog2 (assert_smaller x (x `div` 2))

            go : Nat -> Nat -> Nat
            go n Z = n
            go n (S fuel) = if testBit s n then n else go (S n) fuel

        ||| A rejection: the function, the block, why.
        reject : LocatedIR.Function enc -> LocatedIR.Label -> String -> Either String a
        reject f l why =
          Left ("allocation check: " ++ show f.name ++ ", block " ++ show l ++ ": " ++ why)

        ||| What each block reads before writing it, from the block on: a may
        ||| analysis, over the blocks in postorder, again while anything changes
        ||| when there is a loop.
        covering
        liveIn : Shape enc -> SortedMap LocatedIR.Label Slots
        liveIn sh = go empty
          where
            at : SortedMap LocatedIR.Label Slots -> LocatedIR.Label -> Slots
            at m l = fromMaybe 0 (lookup l m)

            blockIn : SortedMap LocatedIR.Label Slots -> (LocatedIR.Block enc, Summary enc) -> Slots
            blockIn m (b, sm) =
              let out = foldl (\s, l => s .|. at m l) 0 (succs b.term)
              in if null sm.sides then sm.reads .|. minus out sm.writes
                 else
                   let end = out .|. slots (termUses b.term)
                       before = foldr (\(i, u, d), live =>
                                         let live' = maybe live (\l => live .|. at m l) (side i)
                                         in minus live' d .|. u)
                                      end sm.steps
                   in minus before (slots b.params)

            pass : SortedMap LocatedIR.Label Slots -> (SortedMap LocatedIR.Label Slots, Bool)
            pass m = foldl (\(acc, ch), l => case lookup l sh.blocks of
                                                Nothing => (acc, ch)
                                                Just bsm => let new = blockIn acc bsm
                                                            in (insert l new acc,
                                                                ch || new /= at acc l))
                       (m, False) sh.post

            go : SortedMap LocatedIR.Label Slots -> SortedMap LocatedIR.Label Slots
            go m = let (m', changed) = pass m in if changed && sh.loops then go m' else m'

        ||| What is defined at each block's entry on every path: a must analysis
        ||| over the blocks in reverse postorder, again while anything changes
        ||| when there is a loop; a block not reached yet has no entry. The
        ||| function's entry and the resume blocks start from their parameters.
        covering
        definedIn : LocatedIR.Function enc -> Shape enc -> SortedMap LocatedIR.Label Slots
        definedIn f sh = go start
          where
            start : SortedMap LocatedIR.Label Slots
            start = foldl (\m, r => case lookup r sh.blocks of
                                       Just (b, _) => insert r (slots b.params) m
                                       Nothing => m)
                      (singleton f.entry (slots f.params)) (SortedSet.toList sh.resumes)

            -- what the block has defined when it leaves to `to`: at its end, or,
            -- through an overflow there, at the instruction that overflows
            outTo : Slots -> Summary enc -> LocatedIR.Label -> Slots
            outTo inn sm to = inn .|. maybe sm.writes id (lookup to sm.sides)

            atEntry : SortedMap LocatedIR.Label Slots -> LocatedIR.Label -> Maybe Slots
            atEntry m l =
              if l == f.entry || contains l sh.resumes then lookup l m
              else
                let froms = mapMaybe (\p => do inn <- lookup p m
                                               (_, sm) <- lookup p sh.blocks
                                               pure (outTo inn sm l))
                              (fromMaybe [] (lookup l sh.preds))
                in case froms of
                     [] => Nothing
                     (s :: ss) => Just (foldl (.&.) s ss)

            pass : SortedMap LocatedIR.Label Slots -> (SortedMap LocatedIR.Label Slots, Bool)
            pass m = foldr (\l, (acc, ch) => case atEntry acc l of
                                                Nothing => (acc, ch)
                                                Just s =>
                                                  (insert l s acc, ch || Just s /= lookup l acc))
                       (m, False) sh.post

            go : SortedMap LocatedIR.Label Slots -> SortedMap LocatedIR.Label Slots
            go m = let (m', changed) = pass m in if changed && sh.loops then go m' else m'

        ||| One block checked: each use defined, each `live` list complete and
        ||| defined, each continuation the shape of its resume block's parameters.
        checkBlock : LocatedIR.Function enc -> Shape enc -> (gcVisible : Slots) ->
                     SortedMap LocatedIR.Label Slots -> (defined : Slots) ->
                     (LocatedIR.Block enc, Summary enc) -> Either String ()
        checkBlock f sh gcs live inn (b, sm) = do
          let at = \l => fromMaybe 0 (lookup l live)
              out = foldl (\s, l => s .|. at l) 0 (succs b.term)
              afters = if not (any (\(i, _, _) => isJust (collecting i) || directCall i) sm.steps)
                          then map (const 0) sm.steps
                          else if out == 0 && null sm.sides then sm.afters
                          else snd (lives at sm.steps (out .|. slots (termUses b.term)))
          when (minus (sm.reads .|. sm.listed) inn /= 0) $ do
            d <- foldlM definedAt inn sm.steps
            traverse_ (defined d "the terminator reads") (termUses b.term)
          traverse_ instr (zip sm.steps afters)
          whenJust (continuation b.term) resumed
          where
            -- what is live before the instructions, and after each of them
            lives : (LocatedIR.Label -> Slots) -> List (LocatedIR.Instr enc, Slots, Slots) ->
                    (end : Slots) -> (Slots, List Slots)
            lives _ [] end = (end, [])
            lives at ((i, u, d) :: is) end =
              let (after, rest) = lives at is end
                  after' = maybe after (\l => after .|. at l) (side i)
              in (minus after' d .|. u, after :: rest)

            has : Nat -> Slots -> Bool
            has n s = testBit s n

            defined : Slots -> String -> LocatedIR.Location enc -> Either String ()
            defined d what r =
              if has (number r) d then Right ()
              else reject f b.label (what ++ " " ++ show r ++ " before it is written")

            ||| Where a collection can start at the instruction: its `live` list.
            collecting : LocatedIR.Instr enc -> Maybe (List (LocatedIR.Location enc))
            collecting i = case i of
              LocatedIR.Instr.AllocObj _ _ _ live => Just live
              LocatedIR.Instr.AllocSized _ _ _ _ live => Just live
              LocatedIR.Instr.DirectCall _ _ _ True live => Just live
              _ => Nothing

            -- what is defined after the instruction, from what is before:
            -- a rejection for what it reads or lists before it is written
            definedAt : Slots -> (LocatedIR.Instr enc, Slots, Slots) -> Either String Slots
            definedAt d (i, u, w) = do
              when (minus u d /= 0) $ traverse_ (defined d "an instruction reads") (uses i)
              whenJust (collecting i) $ \listed =>
                when (minus (slots listed) d /= 0) $
                  traverse_ (defined d "a live list names") listed
              Right (d .|. w)

            instr : ((LocatedIR.Instr enc, Slots, Slots), Slots) -> Either String ()
            instr ((i, u, w), after) = do
              whenJust (collecting i) $ \listed => do
                let kept = minus after w .|. u
                    missing = minus (kept .&. gcs) (slots listed)
                if missing == 0 then Right ()
                   else reject f b.label (named (lowest missing)
                          ++ " is GC-visible and live where a collection can start, but not listed")
                -- the slow path keeps the slots, and no register
                let held = kept .&. registers
                when (held /= 0) $ reject f b.label (named (lowest held)
                  ++ " is live where a collection can start, which no register survives")
              when (directCall i) $ do
                let across = minus after w .&. registers
                when (across /= 0) $ reject f b.label (named (lowest across)
                  ++ " is live across a direct call, which no register survives")

            resumed : LocatedIR.Cont enc -> Either String ()
            resumed c = do
              case lookup c.resume sh.blocks of
                Nothing =>
                  reject f b.label ("resumes at block " ++ show c.resume ++ ", which is not there")
                Just (r, _) => do
                  let ps = map number r.params
                  if take (length c.live) ps == map number c.live
                        && length ps == S (length c.live)
                     then Right ()
                     else reject f r.label
                            "a resume block's parameters are not its continuation's and the result"
                  let reads = fromMaybe 0 (lookup c.resume live)
                  if reads == 0 then Right ()
                     else reject f r.label ("a resume block reads " ++ named (lowest reads)
                                            ++ ", which its continuation does not keep")
