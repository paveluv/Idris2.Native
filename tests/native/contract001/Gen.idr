-- The runtime contract, checked: generated code calls the runtime's
-- routines by the signatures the contract declares, and a program is
-- lowered only if the runtime's routines have them. A routine is a flat
-- function of the runtime library, so its signature is its form's: the
-- registers of its parameters and of its result.
--
-- The contract declares `exit` as taking one word and returning nothing,
-- as if written
--
--   exit : (status : Bits64) -> Op Heap ()
--
-- and `crash` as taking two words, the message's address and its length.
-- Here the runtime's forms are stood in for by forms of the same names and
-- the signatures each case gives, with bodies that are never run: only the
-- check is shown.
module Main

import Compiler.Native.Lower
import Compiler.Native.Linkage
import Core.FC
import Core.Name
import Core.TT
import Flat.Exp

TestEnc : Enc
TestEnc = defaultEnc

word : String -> FlatVar
word s = MkFlatVar (UN (Basic s)) (SPrim Bits64Type) [Word]

unit : Skeleton
unit = SCon (NS (mkNamespace "Builtin") (UN (Basic "Unit"))) []

||| A form of the name, with the parameters and the result's layout given.
form : Name -> List FlatVar -> Skeleton -> Layout -> FlatDef
form n ps sk lay = MkFlatDef n ps sk lay (FNone EmptyFC) EmptyFC

||| `exit (status : Bits64) : ()`, as the contract has it.
exit : FlatDef
exit = form runtimeExit [word "status"] unit []

||| `crash (message, length : Bits64) : ()`, as the contract has it.
crash : FlatDef
crash = form runtimeCrash [word "message", word "length"] unit []

||| `start (entry, window : Bits64) : ()`, as the contract has it.
start : FlatDef
start = form runtimeStart [word "entry", word "window"] unit []

check : String -> List FlatDef -> IO ()
check what forms = putStrLn $ what ++ ": " ++
  case lowerProgram TestEnc forms [] [] of
    Left err => err
    Right _ => "lowered"

main : IO ()
main = do
  check "as declared" [start, exit, crash]
  check "no exit" [start, crash]
  -- exit (status, code : Bits64) : ()
  check "exit of two words" [start, form runtimeExit [word "status", word "code"] unit [], crash]
  -- crash (message, length : Bits64) : Bits64
  check "crash with a result" [start, exit, form runtimeCrash [word "message", word "length"] (SPrim Bits64Type) [Word]]
