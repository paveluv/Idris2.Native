-- What a program reaches of the runtime, which is what the code generator
-- lowers with it.
--
-- First, the routines of the runtime that the lowering of a program's
-- VMCode may call (`calledRoutines`). The lowering makes some of Idris's
-- primitives calls of the string encoding's routines or of the bignum
-- encoding's, the `Integer` routines: `show (x : Int)` is the cast
-- `cast {to = String} x`, which is one primitive in VMCode, and its code
-- calls the string routine `showSigned` on the integer's word. So the
-- routines a program may call are read off its VMCode, before it is
-- lowered, construct by construct. Each case below is the VMCode of a
-- small Idris program, given by hand, and prints the routines it may
-- call, `string` for the string encoding's and `Integer` for the bignum
-- encoding's, by their names in the runtime. Arithmetic and comparisons
-- on an `Int` call no routine: the lowering makes them of machine
-- instructions alone. `Integer` arithmetic calls one, on the operands
-- beyond the fixnums.
--
-- Then what the program reaches (`programReach`): the flat forms the
-- code generator lowers with it, and the constants marked static whose
-- values it computes as it compiles it. A form is reached from a root
-- (the program's own functions; the routines the seed reaches by their
-- symbols or its VMCode may call; the flat functions that implement its
-- foreign functions) and from a reached form through what it calls, so a
-- routine that is not a root is reached all the same when a reached form
-- calls it. Here three routines stand for the runtime's, in the
-- contract's order, as if declared
--
--   showDouble : Double -> String        -- calls digits and copy,
--                                        -- reads powers
--   append : String -> String -> String  -- calls copy
--   readDouble : String -> Double        -- reads exact, calls halves
--
-- where `powers`, `exact` and `halves` are tables, constants marked
-- static. `showDouble` and `readDouble` read the first two as values;
-- `halves`, which flat code does not hold in one register, `readDouble`
-- computes by calling its form, which calls `half`. A program that shows
-- no double does not reach `showDouble`, so the table `powers` is not
-- computed as it is compiled: the reach saves the compile that work.
-- Each case prints the forms reached, in the order the code generator
-- lowers them, then the marks reached.
module Main

import Compiler.VMCode
import Core.CompileExpr
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.TT.Primitive
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Vect
import Libraries.Data.NameMap
import Native.Codegen.Linkage.Realised
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Lower
import Native.Codegen.ProgramReach
import Native.Flat.Exp
import Native.Intrinsic
import Native.Primitive
import Native.Rep
import Native.Routine
import Native.Types.IntegerRoutine
import Native.Types.StringRoutine

------------------------------------------------------------------------------
-- The routines the lowering may call

||| A function of the runtime's string encoding's module, by its name.
utf8 : String -> Name
utf8 s = NS (supportModule "String.Utf8") (UN (Basic s))

||| A function of the runtime's bignum encoding's module, by its name.
bignum : String -> Name
bignum s = NS (supportModule "Bignum.SignMagnitude") (UN (Basic s))

||| The string routines, by the names the runtime's functions have.
strings : List (Name, StringRoutine)
strings =
  [ (utf8 "length", Length), (utf8 "head", Head), (utf8 "tail", Tail)
  , (utf8 "index", Index), (utf8 "cons", Cons), (utf8 "append", Append)
  , (utf8 "reverse", Reverse), (utf8 "substr", Substr)
  , (utf8 "compare", StringRoutine.Compare), (utf8 "showSigned", ShowSigned)
  , (utf8 "showUnsigned", ShowUnsigned), (utf8 "showDouble", ShowDouble)
  , (utf8 "readDouble", ReadDouble), (utf8 "readWord", ReadWord)
  , (utf8 "textBytes", TextBytes), (utf8 "textAddress", TextAddress)
  , (utf8 "copyText", CopyText), (utf8 "ofText", OfText)
  , (utf8 "after", After), (utf8 "charAt", CharAt), (utf8 "from", From) ]

||| The `Integer` routines, by the names the runtime's functions have.
integers : List (Name, IntegerRoutine)
integers =
  [ (bignum "add", IntegerRoutine.Add), (bignum "sub", IntegerRoutine.Sub)
  , (bignum "mul", IntegerRoutine.Mul), (bignum "div", IntegerRoutine.Div)
  , (bignum "mod", IntegerRoutine.Mod), (bignum "and", IntegerRoutine.And)
  , (bignum "or", IntegerRoutine.Or), (bignum "xor", IntegerRoutine.Xor)
  , (bignum "shl", Shl), (bignum "shr", Shr), (bignum "neg", IntegerRoutine.Neg)
  , (bignum "compare", IntegerRoutine.Compare), (bignum "toBits64", ToBits64)
  , (bignum "fromInt64", FromInt64), (bignum "fromBits64", FromBits64)
  , (bignum "toDecimal", ToDecimal), (bignum "fromDecimal", FromDecimal)
  , (bignum "toDouble", ToDouble), (bignum "fromDouble", FromDouble) ]

||| The contract as a loaded runtime realises it, of the string and
||| bignum encodings' routines alone.
realised : Realised
realised = MkRealised [] (Just strings) (Just integers) empty empty empty empty

||| Each routine by the name generated code calls it by, as printed here:
||| its encoding's word, then its function's name.
labels : SortedMap Name String
labels =
  fromList
    ([(flatName n, "string " ++ nameRoot n) | (n, _) <- strings]
     ++ [(flatName n, "Integer " ++ nameRoot n) | (n, _) <- integers])

||| The routines the definitions' lowering may call, as printed, sorted.
called : List (Name, VMDef) -> String
called defs =
  case sort (map label (Data.SortedSet.toList (calledRoutines realised defs))) of
    [] => "none"
    ls => joinBy ", " ls
  where
    label : Name -> String
    label n = fromMaybe (show n) (lookup n labels)

||| A function of the program, as VMCode has it.
function : String -> VMDef -> (Name, VMDef)
function s d = (NS (mkNamespace "Main") (UN (Basic s)), d)

||| A function of one argument whose body is the primitive of it.
unary : PrimFn 1 -> VMDef
unary fn = MkVMFun [0] [OP RVal fn [Loc 0]]

||| A function of two arguments whose body is the primitive of them.
binary : PrimFn 2 -> VMDef
binary fn = MkVMFun [0, 1] [OP RVal fn [Loc 0, Loc 1]]

||| A function of three arguments whose body is the primitive of them.
ternary : PrimFn 3 -> VMDef
ternary fn = MkVMFun [0, 1, 2] [OP RVal fn [Loc 0, Loc 1, Loc 2]]

||| A function of the compiler's own library that walks a string, by its
||| name: a foreign function, which the lowering makes itself.
iterator : String -> (Name, VMDef)
iterator s =
  (NS (mkNamespace "Libraries.Data.String.Iterator") (UN (Basic s)),
   MkVMForeign [] [CFString, CFInt] CFInt)

||| One case: what the program is, and what its VMCode may call.
scan : String -> List (Name, VMDef) -> IO ()
scan what defs = putStrLn (what ++ ": " ++ called defs)

------------------------------------------------------------------------------
-- What the program reaches

||| A name of a stand-in for a function of the runtime or of the program.
name : String -> String -> Name
name m s = NS (mkNamespace m) (UN (Basic s))

||| A call of a form, with no arguments: only what is called matters here.
call : Name -> Exp
call f = FCall EmptyFC f []

||| A read of a constant marked static as its value.
read : Name -> Exp
read m = FStatic EmptyFC m SOther []

||| A call of a primitive, an extern the code generator binds.
primitive : Name -> Exp
primitive p = FPrim EmptyFC p SOther [] []

||| A stand-in form: a function whose body does each part in turn, as
||| `let _ = part in ...`, and gives nothing. It is never run: only what
||| it calls and reads is followed.
standIn : Name -> List Exp -> FlatDef
standIn n parts =
  MkFlatDef n [] SOther []
    (foldr (FLet EmptyFC (MkFlatVar (UN (Basic "_")) SOther [])) (FNone EmptyFC) parts) EmptyFC

||| The routines' stand-ins, and the functions they call: the table
||| `halves`'s form among them.
showDouble, digits, copy, append, readDouble, halves, half : Name
showDouble = name "Str" "showDouble"
digits = name "Str" "digits"
copy = name "Str" "copy"
append = name "Str" "append"
readDouble = name "Str" "readDouble"
halves = name "Dbl" "halves"
half = name "Dbl" "half"

||| The other constants marked static: two tables of the runtime, read as
||| values, and two constants of the program.
powers, exact, squares, unread : Name
powers = name "Dbl" "powers"
exact = name "Dbl" "exact"
squares = name "Main" "squares"
unread = name "Main" "unread"

||| The program's functions; Linux's functions for the OS services, and
||| the service `write`'s extern; the runtime's implementation of the
||| foreign function that exits.
mainFunction, say, write, writeService, exit, exitImplementation : Name
mainFunction = name "Main" "main"
say = name "Main" "say"
write = name "Linux" "write"
writeService = name "Native.Runtime.OS" "write"
exit = name "Linux" "exit"
exitImplementation = name "Sys" "exit"

||| The forms, by their functions' names: the runtime's routines and what
||| they call, a form of the program, and an implementation of a foreign
||| function, with what each calls and reads.
forms : NameMap FlatDef
forms =
  fromList
    [ (f.name, f)
    | f <- [ standIn showDouble [call digits, call copy, read powers]
           , standIn digits []
           , standIn copy []
           , standIn append [call copy]
           , standIn readDouble [read exact, call halves]
           , standIn halves [call half]
           , standIn half []
           , standIn say [primitive writeService]
           , standIn write []
           , standIn exitImplementation [call exit]
           , standIn exit [] ] ]

||| Each extern bound to the platform's function for it: the OS service
||| `write` to Linux's.
services : SortedMap Name Name
services = fromList [(writeService, write)]

||| The constants marked static, in the order the marks are made.
marks : List Name
marks = [powers, exact, halves, squares, unread]

||| The names, as printed, or `none`.
listed : List Name -> String
listed [] = "none"
listed ns = joinBy ", " (map show ns)

||| One case: what the program is, its VMCode's functions, which of the
||| three routines are its roots (those the seed reaches by their symbols
||| or its VMCode may call), and the implementations of its foreign
||| functions; then the forms and the marks it reaches.
reaching : String -> (functions : List Name) -> (roots : List Name) ->
           (implementations : List Name) -> IO ()
reaching what functions roots implementations =
  let r = programReach forms services functions
            [(n, elem n roots) | n <- [showDouble, append, readDouble]] implementations marks
  in putStrLn (what ++ ": forms " ++ listed (map (\f => f.name) r.forms) ++ "; marks "
               ++ listed r.marks)

main : IO ()
main = do
  -- main = putStrLn "hello": a call of the Prelude's putStrLn, which is
  -- ordinary code, calling no routine itself
  scan "main = putStrLn \"hello\""
    [function "main"
       (MkVMFun []
          [ MKCONSTANT (Loc 0) (Str "hello")
          , CALL RVal True (NS (mkNamespace "Prelude.IO") (UN (Basic "putStrLn"))) [Loc 0] ])]
  -- show (x : Int), the cast to String: the decimal text of the word,
  -- signed; of a Bits8, unsigned; of an Integer, the same of a fixnum
  -- and the bignum encoding's text of one beyond
  scan "show (x : Int)" [function "f" (unary (Cast IntType StringType))]
  scan "show (x : Bits8)" [function "f" (unary (Cast Bits8Type StringType))]
  scan "show (x : Integer)" [function "f" (unary (Cast IntegerType StringType))]
  -- show (x : Double): its shortest decimal text
  scan "show (x : Double)" [function "f" (unary (Cast DoubleType StringType))]
  -- a string read as a number: cast {to = Double} s, cast {to = Int} s,
  -- cast {to = Integer} s
  scan "cast {to = Double} s" [function "f" (unary (Cast StringType DoubleType))]
  scan "cast {to = Int} s" [function "f" (unary (Cast StringType IntType))]
  scan "cast {to = Integer} s" [function "f" (unary (Cast StringType IntegerType))]
  -- x + y: at Int machine instructions alone, at Integer the routine on
  -- operands beyond the fixnums; at Double machine instructions too
  scan "x + y at Int" [function "f" (binary (Add IntType))]
  scan "x + y at Integer" [function "f" (binary (Add IntegerType))]
  scan "x + y at Double" [function "f" (binary (Add DoubleType))]
  -- the rest of Integer's arithmetic, each its own routine: x - y and
  -- x * y; div x y and mod x y, which test y against 0 first, are
  -- prim__div_Integer x y and prim__mod_Integer x y; the negation
  -- primitive, which the Prelude's negate does not use (negate x is
  -- 0 - x) but a program may call, and at Int it calls none; shiftL n i
  -- and shiftR n i of Data.Bits are prim__shl_Integer n i and
  -- prim__shr_Integer n i, the Nat i made an Integer first; and n .&. m,
  -- n .|. m and xor n m
  scan "x - y at Integer" [function "f" (binary (Sub IntegerType))]
  scan "x * y at Integer" [function "f" (binary (Mul IntegerType))]
  scan "prim__div_Integer x y" [function "f" (binary (Div IntegerType))]
  scan "prim__mod_Integer x y" [function "f" (binary (Mod IntegerType))]
  scan "prim__negate_Integer n" [function "f" (unary (Neg IntegerType))]
  scan "prim__negate_Int x" [function "f" (unary (Neg IntType))]
  scan "prim__shl_Integer n i" [function "f" (binary (ShiftL IntegerType))]
  scan "prim__shr_Integer n i" [function "f" (binary (ShiftR IntegerType))]
  scan "n .&. m at Integer" [function "f" (binary (BAnd IntegerType))]
  scan "n .|. m at Integer" [function "f" (binary (BOr IntegerType))]
  scan "xor n m at Integer" [function "f" (binary (BXOr IntegerType))]
  -- comparisons: of strings by the string routines' order, of Integers
  -- by the bignum encoding's, of Ints and Doubles by machine
  -- instructions alone; each of <, <=, ==, >= and > the same way
  scan "s < t at String" [function "f" (binary (LT StringType))]
  scan "s == t at String" [function "f" (binary (EQ StringType))]
  scan "n < m at Integer" [function "f" (binary (LT IntegerType))]
  scan "n <= m at Integer" [function "f" (binary (LTE IntegerType))]
  scan "n == m at Integer" [function "f" (binary (EQ IntegerType))]
  scan "n >= m at Integer" [function "f" (binary (GTE IntegerType))]
  scan "n > m at Integer" [function "f" (binary (GT IntegerType))]
  scan "x < y at Int" [function "f" (binary (LT IntType))]
  scan "x < y at Double" [function "f" (binary (LT DoubleType))]
  -- case s of "a" => 1; _ => 0: the value compared with each string
  scan "case s of \"a\" => 1; _ => 0"
    [function "f"
       (MkVMFun [0]
          [CONSTCASE (Loc 0) [(Str "a", [MKCONSTANT RVal (I 1)])] (Just [MKCONSTANT RVal (I 0)])])]
  -- a primitive in an alternative of a case counts as one anywhere:
  -- \b, s, t => if b then s ++ t else s
  scan "if b then s ++ t else s"
    [function "f"
       (MkVMFun [0, 1, 2]
          [CASE (Loc 0) [(Left 1, [OP RVal StrAppend [Loc 1, Loc 2]])]
             (Just [ASSIGN RVal (Loc 1)])])]
  -- and in a case's default: \n, s, t => case n of 0 => s; _ => s ++ t
  scan "case n of 0 => s; _ => s ++ t"
    [function "f"
       (MkVMFun [0, 1, 2]
          [CONSTCASE (Loc 0) [(I 0, [ASSIGN RVal (Loc 1)])]
             (Just [OP RVal StrAppend [Loc 1, Loc 2]])])]
  -- the string primitives, each its own routine: strLength s; the first
  -- character, prim__strHead s, and the rest, strTail s; strIndex s i;
  -- reverse s; strSubstr i n s, the n characters from the i-th
  scan "strLength s" [function "f" (unary StrLength)]
  scan "prim__strHead s" [function "f" (unary StrHead)]
  scan "strTail s" [function "f" (unary StrTail)]
  scan "strIndex s i" [function "f" (binary StrIndex)]
  scan "reverse s" [function "f" (unary StrReverse)]
  scan "strSubstr i n s" [function "f" (ternary StrSubstr)]
  -- strCons c s, and a character's string, cast {to = String} c, which is
  -- c consed onto the empty string
  scan "strCons c s" [function "f" (binary StrCons)]
  scan "cast {to = String} c" [function "f" (unary (Cast CharType StringType))]
  -- an Integer to and from the fixed-width integers: to one, its value
  -- modulo 2^64; from a 64-bit one beyond the fixnums, a bignum of it;
  -- from a narrow one, always a fixnum, nothing
  scan "cast {to = Int} (n : Integer)" [function "f" (unary (Cast IntegerType IntType))]
  scan "cast {to = Integer} (i : Int)" [function "f" (unary (Cast IntType IntegerType))]
  scan "cast {to = Integer} (b : Bits64)" [function "f" (unary (Cast Bits64Type IntegerType))]
  scan "cast {to = Integer} (b : Bits8)" [function "f" (unary (Cast Bits8Type IntegerType))]
  -- an Integer to and from a double
  scan "cast {to = Double} (n : Integer)" [function "f" (unary (Cast IntegerType DoubleType))]
  scan "cast {to = Integer} d" [function "f" (unary (Cast DoubleType IntegerType))]
  -- the string iterator's functions, which the lowering makes itself:
  -- uncons gives the character at a position and the position after it;
  -- withIteratorString the string from a position on
  scan "the iterator's uncons" [iterator "uncons"]
  scan "the iterator's withIteratorString" [iterator "withIteratorString"]
  -- a definition Idris made an error, which is not lowered, even of a
  -- body that adds Integers
  scan "an error"
    [function "f" (MkVMError [OP RVal (Add IntegerType) [Loc 0, Loc 1]])]
  -- main = putStrLn (s ++ t): the program reaches append, and so copy,
  -- and no constant marked static: no table is computed for it. copy
  -- comes before append, where it is met under showDouble when every
  -- routine is walked
  reaching "appends strings" [mainFunction] [append] []
  -- main = printLn d: showDouble, and what it calls and reads
  reaching "shows a double" [mainFunction] [showDouble] []
  -- each form in its place among every routine's: copy before append,
  -- readDouble after it, halves and half after readDouble
  reaching "appends strings and reads a double" [mainFunction] [append, readDouble] []
  -- squares = map (\n => n * n) [1 .. 10], marked static and read by
  -- main: VMCode has it, so it is computed; unread is marked too, and
  -- nothing reads it
  reaching "reads squares" [mainFunction, squares] [] []
  -- readDouble computes halves by its form, which calls half: both are
  -- reached, and halves is not computed as the program is compiled
  reaching "reads a double" [mainFunction] [readDouble] []
  -- say s = write s, a function of the program marked flat, whose write
  -- is the OS service's extern: Linux's function for it is reached
  reaching "says something" [mainFunction, say] [] []
  -- exitWith (ExitFailure 1): the runtime's flat function that
  -- implements System.prim__exit is reached, and what it calls
  reaching "exits" [mainFunction] [] [exitImplementation]
  -- main = do say (s ++ t); exitWith (ExitFailure 1): a root of each
  -- kind, the program's own say, the routine append and the
  -- implementation of the foreign function that exits; the forms come in
  -- that order, the program's, then the routines', then the
  -- implementations'
  reaching "says, appends and exits" [mainFunction, say] [append] [exitImplementation]
