||| The native backend: `--cg native` pulls VMCode and the flat forms of the
||| functions the program marks flat (`Flat.Marked`) and of what they call,
||| with the shapes of the types they handle (`Flat.Translate.shape`),
||| lowers them to the typed term and through it to
||| the IR, registers allocated and live lists computed
||| (`Compiler.Native.Lower`), renders it as x86-64 instructions
||| (`Compiler.Native.X86.Render`) and links them with the runtime seed into
||| a static ELF (x86-64 Linux). What the lowering does not cover yet is the
||| seed's abort stub, so a program always links and fails with status 70
||| only on the paths that reach it.
|||
||| The runtime is a library of flat functions, the package
||| `idris2-native-runtime`, which a program does not import: the backend
||| loads its modules into the context itself, and its routines, those the
||| runtime contract names (`Compiler.Native.Linkage.routines`), are
||| compiled into every program with the program's own forms.
module Compiler.Native.Native

import Core.Context
import Core.Core
import Core.Directory
import Core.Name
import Compiler.Common
import Compiler.VMCode
import Compiler.Native.LocatedIR
import Compiler.Native.LocatedIR.Dump
import Compiler.Native.Lower
import Compiler.Native.LowerFlat
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value
import Compiler.Native.RegAlloc
import Flat.Exp
import Flat.Marked
import Flat.Problem
import Flat.Translate
import Libraries.Data.NameMap
import Compiler.Native.X86.Asm
import Compiler.Native.X86.Render
import Compiler.Native.X86.Target
import Compiler.Native.Linkage
import Compiler.Native.Link
import Compiler.Native.ELF
import Idris.Syntax
import Data.List
import Data.List1
import Data.SortedMap
import Data.String
import System
import System.File
import Libraries.Utils.Path
import Core.UnifyState
import Idris.Package.Types
import Idris.ProcessIdr
import Idris.SetOptions

%default covering

||| What `--directive` can tell this backend. Directives are shared by every
||| code generator, so ones this backend does not know are ignored.
|||
||| * `cont=heap` or `cont=stack`: how continuations are realised. Only the
|||   heap lowering exists, so `stack` is refused: a harness that asks for it
|||   learns so, instead of testing the heap lowering twice.
||| * `nursery=<bytes>`: the size of the allocation window, a multiple of 8
|||   from 8 to 2^30. Tests use a tiny window so that allocation-heavy code
|||   takes the slow path often and, once the runtime can collect, collects
|||   often too.
||| * `flat <name>...`: the functions the program marks flat (`Flat.Marked`).
||| * `dump-flat=<file>`: write the flat forms, and the shapes of their data
|||   types, to the file.
||| * `dump-ir=<file>`: write the IR the produce pass makes to the file.
||| * `dump-asm=<file>`: write the rendered instructions to the file, in Intel
|||   syntax, with each function's name before its code.
||| * `val-encoding=tag1`, `tag0` or `nofixnums`: how a uniform value is a word
|||   (`ValEnc` in `Compiler.Native.HeapObject`): fixnum tag 1, the
|||   default; fixnum tag 0; or no fixnums, every integer boxed, which is not
|||   implemented yet and so is refused.
||| * `target=<arch>-<os>`: the platform the program is compiled for
|||   (`Compiler.Native.Platform`), `x86_64-linux` by default; one not built
|||   yet is refused by name.
record Settings where
  constructor MkSettings
  window : Int
  dumpFlat : Maybe String
  dumpIr : Maybe String
  dumpAsm : Maybe String
  encodings : Enc
  platform : Platform

parseSettings : List String -> Either String Settings
parseSettings = foldlM setting (MkSettings windowBytes Nothing Nothing Nothing defaultEnc defaultPlatform)
  where
    setting : Settings -> String -> Either String Settings
    setting o d = case forget (split (== '=') d) of
      ["cont", "heap"] => Right o
      ["cont", "stack"] => Left "the stack lowering of continuations is not implemented"
      ["cont", v] => Left ("cont= takes heap or stack, not " ++ show v)
      ["nursery", v] => case parsePositive {a = Integer} v of
        Just n => if n >= 8 && n <= 1073741824 && n `mod` 8 == 0
                     then Right ({ window := cast n } o)
                     else Left ("nursery= takes a multiple of 8 from 8 to 2^30, not " ++ v)
        Nothing => Left ("nursery= takes a number of bytes, not " ++ show v)
      ["dump-flat", path] => Right ({ dumpFlat := Just path } o)
      ["dump-ir", path] => Right ({ dumpIr := Just path } o)
      ["dump-asm", path] => Right ({ dumpAsm := Just path } o)
      ["val-encoding", "tag1"] => Right ({ encodings.val := FixnumTag1 } o)
      ["val-encoding", "tag0"] => Right ({ encodings.val := FixnumTag0 } o)
      ["val-encoding", "nofixnums"] => Left "the encoding nofixnums, every integer boxed, is not implemented"
      ["val-encoding", v] => Left ("val-encoding= takes tag1, tag0 or nofixnums, not " ++ show v)
      ["target", v] => case parsePlatform v of
        Just p => if built p then Right ({ platform := p } o)
                  else Left ("the target " ++ show p ++ " is not implemented; only x86_64-linux is")
        Nothing => Left ("target= takes <arch>-<os>, such as x86_64-linux, not " ++ show v)
      _ => Right o

||| Of the flat forms, those of the functions named and of the forms they
||| call, the functions of the OS services they call among them, and the
||| shapes of the data types among their types.
flatInputs : {auto c : Ref Ctxt Defs} -> NameMap FlatDef -> List (Name, Name) -> List Name ->
             Core (List FlatDef, Shapes)
flatInputs table services roots = do
  forms <- reach empty [] roots
  let skeletons = nub (filter isData (concatMap formSkeletons forms))
  shapes <- traverse (\sk => map (sk,) <$> shape sk) skeletons
  pure (forms, catMaybes shapes)
  where
    isData : Skeleton -> Bool
    isData (SCon _ _) = True
    isData _ = False

    reach : SortedMap Name () -> List FlatDef -> List Name -> Core (List FlatDef)
    reach seen acc [] = pure (reverse acc)
    reach seen acc (n :: ns) =
      if isJust (Data.SortedMap.lookup n seen) then reach seen acc ns else do
        Just fd <- pure (lookup n table)
          | Nothing => reach (insert n () seen) acc ns
        reach (insert n () seen) (fd :: acc)
              (formCallees fd ++ mapMaybe (\p => Data.List.lookup p services) (formPrims fd) ++ ns)

||| From VMCode to the image, under encodings whose value encoding has
||| fixnums: produce the term, allocate its registers, render, link.
pipeline : {auto c : Ref Ctxt Defs} -> (enc : Enc) -> {auto 0 _ : HasFixnums enc.val} ->
           Settings -> NameMap FlatDef -> List (Name, VMDef) -> Core (List Bits8)
pipeline enc settings table defs = do
  (forms, shapes) <- flatInputs table (serviceBindings {enc} settings.platform)
                                (map fst defs ++ [r.name | r <- routines {enc}, r.provided])
  Right (_ ** term) <- pure (lowerProgram enc settings.platform forms shapes defs)
    | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
  let ir = allocRegs x86_64 term
  case settings.dumpIr of
    Just path => do
      Right () <- coreLift (writeFile path (dumpProgram ir))
        | Left err => throw (FileErr path err)
      pure ()
    Nothing => pure ()
  let Right rendered = render enc ir
    | Left err => throw (InternalError ("native: " ++ err))
  case settings.dumpAsm of
    Just path => do
      Right () <- coreLift (writeFile path (unlines (map show rendered.text)))
        | Left err => throw (FileErr path err)
      pure ()
    Nothing => pure ()
  let Right image = linkProgram enc settings.window rendered.areas rendered.text rendered.rodata
    | Left problems => throw (InternalError ("native: the image cannot be assembled: " ++ show problems))
  pure image

||| The intrinsics and the OS services the loaded runtime declares, each
||| checked against the contract (`Compiler.Native.Linkage.intrinsics`,
||| `osServices`): an `%extern` whose arguments lay out as the declared
||| registers, the token among them taking none, and whose result lays out
||| as the declared ones. What differs is reported; one the runtime does not
||| declare is not missed.
checkIntrinsics : {auto c : Ref Ctxt Defs} -> (enc : Enc) -> Core (List String)
checkIntrinsics enc
    = catMaybes <$> traverse one ([(i.name, "an intrinsic", i.params, i.results) | i <- intrinsics {enc}]
                                  ++ [(serviceExtern s, "an OS service", s.params, s.results) | s <- osServices {enc}])
  where
    -- the registers of the arguments, then of the result
    walk : ClosedNF -> Core (Either String (List (Ty enc), List (Ty enc)))
    walk (NBind bfc x (Pi _ _ _ aty) sc) = do
      defs <- get Ctxt
      Right (_, lay) <- laidOut !(evalClosure defs aty)
        | Left _ => pure (Left ("its argument " ++ show x ++ " is not flat"))
      Right (ps, rs) <- walk !(sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound x)))
        | Left e => pure (Left e)
      pure (Right (tys lay ++ ps, rs))
    walk res = do
      Right (_, lay) <- laidOut res
        | Left _ => pure (Left "its result is not flat")
      pure (Right ([], tys lay))

    one : (Name, String, List (Ty enc), List (Ty enc)) -> Core (Maybe String)
    one (n, what, params, results) = do
      defs <- get Ctxt
      Just gdef <- lookupCtxtExact n (gamma defs)
        | Nothing => pure Nothing
      let ExternDef _ = definition gdef
        | _ => pure (Just (show n ++ " is " ++ what ++ " of the native code generator, but is not declared %extern"))
      Right (ps, rs) <- walk !(nf defs Env.empty (type gdef))
        | Left e => pure (Just (show n ++ ": " ++ e))
      pure $ if ps == params && rs == results then Nothing
             else Just (show n ++ " is declared as " ++ show ps ++ " -> " ++ show rs
                        ++ ", but the native code generator provides it as "
                        ++ show params ++ " -> " ++ show results)

||| Load the runtime's modules into the context: the module `Runtime`, which
||| imports the generic ones, and the platform's module, which implements
||| the OS services and which nothing generic imports, from the installed
||| package, with the backend's own package, whose
||| `Compiler.Native.HeapObject` the runtime shares.
loadRuntime : {auto c : Ref Ctxt Defs} -> {auto s : Ref Syn SyntaxInfo} -> Platform -> Core ()
loadRuntime platform = do
  addPkgDir "idris2-native-runtime" anyBounds
  addPkgDir "idris2-native" anyBounds
  u <- newRef UST initUState
  traverse_ (\ns => addImport (MkImport EmptyFC False (nsAsModuleIdent ns) ns))
            (mkNamespace "Runtime" :: toList (platformModule platform))

compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c s _ outputDir tm outfile = do
  Right settings <- parseSettings <$> getDirectives markingCG
    | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
  Just table <- markedForms (loadRuntime settings.platform)
    | Nothing => pure Nothing
  [] <- checkIntrinsics settings.encodings
    | errs => throw (GenericMsg EmptyFC ("native: " ++ fastConcat (intersperse "\n" errs)))
  whenJust settings.dumpFlat $ \f => dumpFlat f table
  cdata <- getCompileData False VMCode tm
  image <- case settings.encodings of
    MkEnc FixnumTag1 b => pipeline (MkEnc FixnumTag1 b) settings table (vmcode cdata)
    MkEnc FixnumTag0 b => pipeline (MkEnc FixnumTag0 b) settings table (vmcode cdata)
    MkEnc NoFixnums _ => throw (GenericMsg EmptyFC "native: the encoding nofixnums is not implemented")
  coreLift_ $ mkdirAll outputDir
  let outexec = outputDir </> outfile
  Right () <- coreLift (writeImage outexec image)
    | Left err => throw (FileErr outexec err)
  pure (Just outexec)

executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm = do
  Just exe <- compileExpr c s tmpDir tmpDir tm "_tmp_native"
    | Nothing => throw (InternalError "native: compilation failed")
  coreLift_ $ system [exe]

export
codegenNative : Codegen
codegenNative = MkCG compileExpr executeExpr Nothing Nothing
