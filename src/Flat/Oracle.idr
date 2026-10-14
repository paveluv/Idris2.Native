||| The flat oracle, `--cg flat-oracle`: the program compiled by the Chez code
||| generator, each function that has a flat form compiled from that form,
||| made ordinary again (`Flat.Translate.forget`). It runs as the program does
||| exactly when the translation keeps each function's meaning, which is what
||| the tests of the translation check.
|||
||| It understands one directive of its own, `dump-flat=<file>`, which writes
||| the flat forms and the shapes of their data types to the file.
module Flat.Oracle

import Compiler.Common
import Compiler.Scheme.Chez
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Options
import Core.TT.Term
import Data.List1
import Data.String
import Flat.Exp
import Flat.Marked
import Flat.Translate
import Idris.Syntax
import Libraries.Data.NameMap

%default covering

||| The file the directives ask the flat forms to be written to.
export
dumpFlatFile : List String -> Maybe String
dumpFlatFile [] = Nothing
dumpFlatFile (d :: ds) = case forget (split (== '=') d) of
  ["dump-flat", path] => Just path
  _ => dumpFlatFile ds

-- The program's flat forms, used in place of their functions' ordinary
-- forms: whether there are, or errors have been reported already.
useForms : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> Core Bool
useForms
    = do Just forms <- markedForms (pure ())
           | Nothing => pure False
         whenJust (dumpFlatFile !(getDirectives (Other "flat-oracle"))) $ \f => dumpFlat f forms
         useFlatForms forms
         pure True

compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c s tmpDir outputDir tm outfile
    = if !useForms then codegenChez.compileExpr c s tmpDir outputDir tm outfile else pure Nothing

executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm
    = when !useForms $ codegenChez.executeExpr c s tmpDir tm

export
codegenFlatOracle : Codegen
codegenFlatOracle = MkCG compileExpr executeExpr Nothing Nothing
