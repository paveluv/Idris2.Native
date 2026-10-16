||| Idris's operations on machine words, as every producer of the term IR
||| (`Native.Codegen.TermIR.Program`) writes them: what `div`, `mod` and the shifts
||| of a 64-bit word mean. Each is `Build` code, in a function of either
||| convention, so that ordinary code and flat code compute the same.
module Native.Codegen.Words

import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.TermIR.Build as TermIR
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd as TermIR

import Data.List.Quantifiers
import Native.Types.Enc as Types
%default total

parameters {0 enc : Types.Enc} {0 d : TermIR.Decls enc} {0 c : IRCommon.Conv enc} {0 m : Bool}
           {0 v : IRCommon.Ty enc -> Type} {0 l : List (IRCommon.Ty enc) -> Type}

  ||| The quotient or the remainder of the word `a` by the word `b`, which is
  ||| not 0: Euclidean when signed, so that the remainder is never negative,
  ||| as Idris divides, and on the words as unsigned otherwise. The most
  ||| negative word divided by −1 wraps to itself, with remainder 0.
  export
  divide : (signed, remainder : Bool) -> (a, b : TermIR.Opnd v IRCommon.Ty.W64) ->
           TermIR.Build d c m v l (TermIR.Opnd v IRCommon.Ty.W64)
  divide False r a b = TermIR.Build.emit1 (TermIR.Instr.Arith (if r then IRCommon.Op.RemU else IRCommon.Op.DivU) a b)
  divide True r a b = do
    [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
      TermIR.Build.branch IRCommon.Op.EqR b (TermIR.Opnd.W (-1))
        (if r then done [TermIR.Opnd.W 0] else do n <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate a)
                                                  done [n])
        (do q <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.DivS a b)
            rm <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.RemS a b)
            TermIR.Build.branch IRCommon.Op.LtS rm (TermIR.Opnd.W 0)
              (TermIR.Build.branch IRCommon.Op.GtS b (TermIR.Opnd.W 0)
                 (do q' <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Sub q (TermIR.Opnd.W 1))
                     rm' <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Add rm b)
                     done [if r then rm' else q'])
                 (do q' <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Add q (TermIR.Opnd.W 1))
                     rm' <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Sub rm b)
                     done [if r then rm' else q']))
              (done [if r then rm else q]))
    pure w

  ||| The Prelude's `div` and `mod` never pass 0 to the primitive, so a 0
  ||| here crashes.
  export
  nonZero : TermIR.Opnd v IRCommon.Ty.W64 -> TermIR.Build d c m v l ()
  nonZero b = TermIR.Build.leaveIf IRCommon.Op.EqR b (TermIR.Opnd.W 0) (TermIR.Build.crash "division by zero")

  ||| A shift of the word `a` by the count `n`, a word, as Idris shifts: by 64
  ||| or more, a left or logical right shift gives 0 and an arithmetic one the
  ||| sign. A negative count counts as such a count.
  export
  shiftBy : IRCommon.Op.ArithOp -> (a, n : TermIR.Opnd v IRCommon.Ty.W64) ->
            TermIR.Build d c m v l (TermIR.Opnd v IRCommon.Ty.W64)
  shiftBy o a n = do
    [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
      TermIR.Build.branch IRCommon.Op.GtU n (TermIR.Opnd.W 63)
        (case o of
           IRCommon.Op.Sar => do w <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Sar a (TermIR.Opnd.W 63))
                                 done [w]
           _ => done [TermIR.Opnd.W 0])
        (do w <- TermIR.Build.emit1 (TermIR.Instr.Arith o a n); done [w])
    pure w
