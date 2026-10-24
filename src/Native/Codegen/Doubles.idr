||| Idris's casts between doubles and the integer types' words, as every
||| producer of the term IR (`Native.Codegen.TermIR.Program`) writes them,
||| so that ordinary code and flat code compute the same. Each is `Build`
||| code, in a function of either convention.
|||
||| A finite double cast to an integer type is its exact truncation toward
||| zero, wrapped to the type's width as a cast from `Integer` wraps, so that
||| a cast from `Double` to `Int` is the cast from `Integer` to `Int` after
||| the one from `Double` to `Integer`; NaN and the infinities are 0, the
||| cast's failure value. The Chez backend agrees for every finite double
||| and ends the program for the others; the machines do not agree with
||| each other there (x86's truncation gives its integer indefinite, the
||| word 2^63, and AArch64's saturates), so neither is the meaning.
module Native.Codegen.Doubles

import Native.Codegen.IRCommon.Conv as IRCommon
import Native.Codegen.IRCommon.Op
import Native.Codegen.IRCommon.Ty as IRCommon
import Native.Codegen.TermIR.Build as TermIR
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Instr
import Native.Codegen.TermIR.IsInt
import Native.Codegen.TermIR.Opnd as TermIR
import Native.Codegen.Words

import Data.List.Quantifiers
import Native.Types.Enc as Types
import Native.Width

%default total

parameters {0 enc : Types.Enc} {0 d : TermIR.Decls enc} {0 c : IRCommon.Conv enc} {0 m : Bool}
           {0 v : IRCommon.Ty enc -> Type} {0 l : List (IRCommon.Ty enc) -> Type}

  ||| A double as the integer type of the width and sign: truncated toward
  ||| zero, exactly, and wrapped to the width. A double from -2^63 up to
  ||| 2^63 is converted by the machine's truncation, which is exact there.
  ||| Any other finite double is a whole number, its significand times 2 to
  ||| the 11th power or more, so its value modulo 2^64 is the significand
  ||| shifted up as far as its exponent says, 0 from 64 places on. NaN and
  ||| the infinities, whose exponent field is all ones, are 0.
  export
  toWord : (Width, Bool) -> TermIR.Opnd v IRCommon.Ty.F64 ->
           TermIR.Build d c m v l (TermIR.Opnd v IRCommon.Ty.W64)
  toWord h f = do
    low <- TermIR.Build.emit1 (TermIR.Instr.FConst (-9223372036854775808.0))
    high <- TermIR.Build.emit1 (TermIR.Instr.FConst 9223372036854775808.0)
    -- both comparisons are false for NaN
    above <- TermIR.Build.emit1 (TermIR.Instr.FCmp IRCommon.Op.GeS f low)
    below <- TermIR.Build.emit1 (TermIR.Instr.FCmp IRCommon.Op.LtS f high)
    inside <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.And above below)
    [w] <- TermIR.Build.joinPoint [IRCommon.Ty.W64] $ \done =>
      TermIR.Build.branch IRCommon.Op.NeR inside (TermIR.Opnd.W 0)
        (do w <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.F2I f)
            done [w]) $ do
        b <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.FBits f)
        e0 <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Shr b (TermIR.Opnd.W 52))
        e <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.And e0 (TermIR.Opnd.W 0x7FF))
        TermIR.Build.branch IRCommon.Op.EqR e (TermIR.Opnd.W 0x7FF) (done [TermIR.Opnd.W 0]) $ do
          m0 <- TermIR.Build.emit1
            (TermIR.Instr.Arith IRCommon.Op.And b (TermIR.Opnd.W 0xFFFFFFFFFFFFF))
          m <- TermIR.Build.emit1
            (TermIR.Instr.Arith IRCommon.Op.Or m0 (TermIR.Opnd.W 0x10000000000000))
          -- the places the significand moves up: the exponent less its bias and
          -- the significand's 52 bits after the point
          s <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Sub e (TermIR.Opnd.W 1075))
          TermIR.Build.branch IRCommon.Op.GeS s (TermIR.Opnd.W 64) (done [TermIR.Opnd.W 0]) $ do
            u <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Shl m s)
            TermIR.Build.branch IRCommon.Op.LtS b (TermIR.Opnd.W 0)
              (do n <- TermIR.Build.emit1 (TermIR.Instr.Unary IRCommon.Op.Negate u)
                  done [n])
              (done [u])
    Words.wrap h w

  ||| A word of the integer type of the width and sign as the nearest double,
  ||| ties to even, as the machine's conversion rounds. A `Bits64` at or
  ||| above 2^63 is halved, its low bit kept for the rounding, converted and
  ||| doubled.
  export
  fromWord : (Width, Bool) -> TermIR.Opnd v IRCommon.Ty.W64 ->
             TermIR.Build d c m v l (TermIR.Opnd v IRCommon.Ty.F64)
  fromWord (Width.Whole, False) w = do
    [f] <- TermIR.Build.joinPoint [IRCommon.Ty.F64] $ \done =>
      TermIR.Build.branch IRCommon.Op.GeS w (TermIR.Opnd.W 0)
        (do f <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F w)
            done [f]) $ do
        h <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Shr w (TermIR.Opnd.W 1))
        b <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.And w (TermIR.Opnd.W 1))
        hb <- TermIR.Build.emit1 (TermIR.Instr.Arith IRCommon.Op.Or h b)
        f <- TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F hb)
        f2 <- TermIR.Build.emit1 (TermIR.Instr.FArith IRCommon.Op.FAdd f f)
        done [f2]
    pure f
  fromWord _ w = TermIR.Build.emit1 (TermIR.Instr.Convert IRCommon.Op.I2F w)
