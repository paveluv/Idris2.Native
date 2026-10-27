||| `flat-check`: the check of a module's flat functions as the module is
||| built, and the code generator's own of the module, as a code generator,
||| since that is what Idris runs then.
module Native.Flat.Check

import Native.Flat.Marked

import Compiler.Common
import Core.Context
import Core.Context.Context
import Core.Core
import Core.FC
import Core.Name
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
|||
||| The backend's primitives are the code generator's to name
||| (`primitives`), by their types; and the code generator checks what it
||| needs of each module as it is built (`moduleCheck`), before its flat
||| functions are checked: as it is built, a module's own definitions are
||| at hand as elaborated, where a program's compilation would decode them
||| to look.
export
codegenFlatCheck : (primitives : Ref Ctxt Defs -> Core (List Name)) ->
                   (moduleCheck : Ref Ctxt Defs -> Core ()) -> Codegen
codegenFlatCheck primitives moduleCheck = MkCG compileExpr executeExpr (Just check) Nothing
  where
    nothing : Core a
    nothing =
      throw
        (GenericMsg EmptyFC "flat-check only checks modules as they are built; it compiles nothing")

    compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String -> ClosedTerm -> String ->
                  Core (Maybe String)
    compileExpr _ _ _ _ _ _ = nothing

    executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
    executeExpr _ _ _ _ = nothing

    check : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> (sourceFile : String) ->
            Core (Maybe (String, List String))
    check c s sourceFile
        = do moduleCheck c
             Marked.checkModule primitives sourceFile
             pure (Just (sourceFile, []))
