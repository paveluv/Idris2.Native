||| Idris's operations on machine words, as every producer of the term IR
||| (`Compiler.Native.TermIR.Program`) writes them: what `div`, `mod` and the shifts
||| of a 64-bit word mean. Each is `Build` code, in a function of either
||| convention, so that ordinary code and flat code compute the same.
module Compiler.Native.Words

import Compiler.Native.HeapObject.Enc
import Compiler.Native.IRCommon.Conv
import Compiler.Native.IRCommon.Operators.ArithOp
import Compiler.Native.IRCommon.Operators.Rel
import Compiler.Native.IRCommon.Operators.UnOp
import Compiler.Native.IRCommon.Ty
import Compiler.Native.TermIR.Build
import Compiler.Native.TermIR.Decls
import Compiler.Native.TermIR.Instr
import Compiler.Native.TermIR.IsInt
import Compiler.Native.TermIR.Opnd

import Data.List.Quantifiers
%default total

parameters {0 enc : Enc} {0 d : Decls enc} {0 c : Conv enc} {0 m : Bool}
           {0 v : Ty enc -> Type} {0 l : List (Ty enc) -> Type}

  ||| The quotient or the remainder of the word `a` by the word `b`, which is
  ||| not 0: Euclidean when signed, so that the remainder is never negative,
  ||| as Idris divides, and on the words as unsigned otherwise. The most
  ||| negative word divided by −1 wraps to itself, with remainder 0.
  export
  divide : (signed, remainder : Bool) -> (a, b : Opnd v W64) -> Build d c m v l (Opnd v W64)
  divide False r a b = emit1 (Arith (if r then RemU else DivU) a b)
  divide True r a b = do
    [w] <- joinPoint [W64] $ \done =>
      branch EqR b (W (-1))
        (if r then done [W 0] else do n <- emit1 (Unary Negate a); done [n])
        (do q <- emit1 (Arith DivS a b)
            rm <- emit1 (Arith RemS a b)
            branch LtS rm (W 0)
              (branch GtS b (W 0)
                 (do q' <- emit1 (Arith Sub q (W 1)); rm' <- emit1 (Arith Add rm b); done [if r then rm' else q'])
                 (do q' <- emit1 (Arith Add q (W 1)); rm' <- emit1 (Arith Sub rm b); done [if r then rm' else q']))
              (done [if r then rm else q]))
    pure w

  ||| The Prelude's `div` and `mod` never pass 0 to the primitive, so a 0
  ||| here crashes.
  export
  nonZero : Opnd v W64 -> Build d c m v l ()
  nonZero b = leaveIf EqR b (W 0) (crash "division by zero")

  ||| A shift of the word `a` by the count `n`, a word, as Idris shifts: by 64
  ||| or more, a left or logical right shift gives 0 and an arithmetic one the
  ||| sign. A negative count counts as such a count.
  export
  shiftBy : ArithOp -> (a, n : Opnd v W64) -> Build d c m v l (Opnd v W64)
  shiftBy o a n = do
    [w] <- joinPoint [W64] $ \done =>
      branch GtU n (W 63)
        (case o of
           Sar => do w <- emit1 (Arith Sar a (W 63)); done [w]
           _ => done [W 0])
        (do w <- emit1 (Arith o a n); done [w])
    pure w
