||| `flat-check`: the check of a module's flat functions as the module is
||| built, as a code generator, since that is what Idris runs then.
module Flat.Check

import Flat.Marked

import Compiler.Common
import Core.Context
import Core.Context.Context
import Core.Core
import Core.FC
import Core.TT.Term
import Idris.Syntax

%default covering

||| The code generator `flat-check`, which compiles nothing: as an incremental
||| code generator (`--inc flat-check`), it checks each module's flat
||| functions as the module is built (`checkModule`), and records the source
||| file as its data. It is not the native code generator, because Idris stops
||| treating the code generator in use as incremental as soon as an imported
||| module, such as the Prelude, was built without it, which would turn the
||| check off under `--cg native` and rebuild every module each time.
export
codegenFlatCheck : Codegen
codegenFlatCheck = MkCG compileExpr executeExpr (Just check) Nothing
  where
    nothing : Core a
    nothing = throw (GenericMsg EmptyFC "flat-check only checks modules as they are built; it compiles nothing")

    compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String -> ClosedTerm -> String -> Core (Maybe String)
    compileExpr _ _ _ _ _ _ = nothing

    executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
    executeExpr _ _ _ _ = nothing

    check : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> (sourceFile : String) -> Core (Maybe (String, List String))
    check c s sourceFile
        = do checkModule sourceFile
             pure (Just (sourceFile, []))
