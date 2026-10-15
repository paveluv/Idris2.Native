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
||| runtime contract names (`routines` in `Compiler.Native.Linkage.Routine`), are
||| compiled into every program with the program's own forms.
module Compiler.Native.Native

import Compiler.Native.ELF
import Compiler.Native.HeapObject.BignumEnc as HeapObject
import Compiler.Native.HeapObject.Enc as HeapObject
import Compiler.Native.HeapObject.StringEnc as HeapObject
import Compiler.Native.HeapObject.ValEnc
import Compiler.Native.IRCommon.Ty as IRCommon
import Compiler.Native.Link
import Compiler.Native.Linkage.ForeignFunctions
import Compiler.Native.Linkage.InlineExtern
import Compiler.Native.Linkage.OSService as Linkage
import Compiler.Native.Linkage.Routine as Linkage
import Compiler.Native.LocatedIR.Dump
import Compiler.Native.LocatedIR.Program as LocatedIR
import Compiler.Native.Lower
import Compiler.Native.LowerFlat
import Compiler.Native.Platform
import Compiler.Native.RegAlloc
import Compiler.Native.TermIR.Decls as TermIR
import Compiler.Native.TermIR.Program as TermIR
import Compiler.Native.X86.Asm
import Compiler.Native.X86.Encode
import Compiler.Native.X86.Render
import Compiler.Native.X86.Target

import Algebra.Semiring
import Algebra.ZeroOneOmega
import Compiler.Common
import Compiler.VMCode
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Directory
import Core.Env
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Name.Scoped
import Core.Normalise.Eval
import Core.Options
import Core.TT.Binder
import Core.TT.Term
import Core.UnifyState
import Core.Value
import Data.Builder as Data
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.String
import Data.WriteBuilder
import Flat.Exp
import Flat.Marked
import Flat.Problem
import Flat.Translate
import Idris.Package.Types
import Idris.ProcessIdr
import Idris.SetOptions
import Idris.Syntax
import Libraries.Data.NameMap
import Libraries.Utils.Path
import System
import System.Clock
import System.File
import System.File.ReadWrite

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
||| * `dump-foreign=<file>`: write the foreign functions and externs of the
|||   program's libraries, each with how this backend implements it.
||| * `val-encoding=tag1`, `tag0` or `nofixnums`: how a uniform value is a word
|||   (`Compiler.Native.HeapObject.ValEnc`): fixnum tag 1, the
|||   default; fixnum tag 0; or no fixnums, every integer boxed, which is not
|||   implemented yet and so is refused.
||| * `string-encoding=utf8` or `utf32`: how a `String` is laid out
|||   (`StringEnc`): UTF-8 with the ASCII bit, the default, or UTF-32,
|||   which is not implemented yet and so is refused.
||| * `target=<arch>-<os>`: the platform the program is compiled for
|||   (`Compiler.Native.Platform`), `x86_64-linux` by default; one not built
|||   yet is refused by name.
record Settings where
  constructor MkSettings
  window : Int
  dumpFlat : Maybe String
  dumpIr : Maybe String
  dumpAsm : Maybe String
  dumpForeign : Maybe String
  encodings : HeapObject.Enc
  platform : Platform

export
codegenNative : Codegen
codegenNative = MkCG compileExpr executeExpr Nothing Nothing
  where
    compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                  (tmpDir : String) -> (outputDir : String) ->
                  ClosedTerm -> (outfile : String) -> Core (Maybe String)
    compileExpr c s _ outputDir tm outfile = do
      Right settings <- parseSettings <$> getDirectives Flat.Marked.markingCG
        | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
      Just table <- phase "the runtime loaded"
        (Flat.Marked.markedForms (loadRuntime settings.platform settings.encodings))
        | Nothing => pure Nothing
      [] <- phase "the contract checked" (checkExterns settings.encodings)
        | errs => throw (GenericMsg EmptyFC ("native: " ++ fastConcat (intersperse "\n" errs)))
      whenJust settings.dumpFlat $ \f => dumpFlat f table
      whenJust settings.dumpForeign $ \f => dumpForeign settings.encodings f
      cdata <- phase "Idris's passes" (getCompileData False VMCode tm)
      image <- case settings.encodings of
        HeapObject.Enc.MkEnc HeapObject.ValEnc.FixnumTag1 b s =>
          pipeline (HeapObject.Enc.MkEnc HeapObject.ValEnc.FixnumTag1 b s) settings table (vmcode cdata)
        HeapObject.Enc.MkEnc HeapObject.ValEnc.FixnumTag0 b s =>
          pipeline (HeapObject.Enc.MkEnc HeapObject.ValEnc.FixnumTag0 b s) settings table (vmcode cdata)
        HeapObject.Enc.MkEnc HeapObject.ValEnc.NoFixnums _ _ =>
          throw (GenericMsg EmptyFC "native: the encoding nofixnums is not implemented")
      coreLift_ $ mkdirAll outputDir
      let outexec = outputDir </> outfile
      Right () <- phase "the image written" (coreLift (ELF.writeImage outexec image))
        | Left err => throw (FileErr outexec err)
      pure (Just outexec)
      where
        parseSettings : List String -> Either String Settings
        parseSettings =
          foldlM setting
            (MkSettings Link.windowBytes Nothing Nothing Nothing Nothing HeapObject.Enc.defaultEnc
             Platform.defaultPlatform)
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
              ["dump-foreign", path] => Right ({ dumpForeign := Just path } o)
              ["val-encoding", "tag1"] => Right ({ encodings.val := HeapObject.ValEnc.FixnumTag1 } o)
              ["val-encoding", "tag0"] => Right ({ encodings.val := HeapObject.ValEnc.FixnumTag0 } o)
              ["val-encoding", "nofixnums"] => Left "the encoding nofixnums, every integer boxed, is not implemented"
              ["val-encoding", v] => Left ("val-encoding= takes tag1, tag0 or nofixnums, not " ++ show v)
              ["string-encoding", "utf8"] => Right ({ encodings.string := HeapObject.StringEnc.Utf8 } o)
              ["string-encoding", "utf32"] => Left "the string encoding utf32 is not implemented"
              ["string-encoding", v] => Left ("string-encoding= takes utf8 or utf32, not " ++ show v)
              ["target", v] => case Platform.parsePlatform v of
                Just p => if Platform.built p then Right ({ platform := p } o)
                          else Left ("the target " ++ show p ++ " is not implemented; only x86_64-linux is")
                Nothing => Left ("target= takes <arch>-<os>, such as x86_64-linux, not " ++ show v)
              _ => Right o

        ||| The inline externs and the OS services the loaded runtime declares, each
        ||| checked against the contract (`inlineExterns` in
        ||| `Compiler.Native.Linkage.InlineExtern`, `osServices` in
        ||| `Compiler.Native.Linkage.OSService`): an `%extern` whose arguments lay out as the declared
        ||| registers, the token among them taking none, and whose result lays out
        ||| as the declared ones. What differs is reported; one the runtime does not
        ||| declare is not missed.
        checkExterns : (enc : HeapObject.Enc) -> Core (List String)
        checkExterns enc
            = catMaybes <$> traverse one
              ([(i.name, "an inline extern", i.params, i.results) | i <- Linkage.InlineExtern.inlineExterns {enc}]
                                          ++
                                            [(Linkage.OSService.serviceExtern s, "an OS service", s.params, s.results)
                                             | s <- Linkage.OSService.osServices {enc}])
          where
            -- the registers of the arguments, then of the result
            walk : ClosedNF -> Core (Either String (List (IRCommon.Ty enc), List (IRCommon.Ty enc)))
            walk (NBind bfc x (Pi _ rig _ aty) sc) = do
              defs <- get Ctxt
              let False = isErased rig
                | True => walk !(sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound x)))
              Right (_, lay) <- Flat.Translate.laidOut !(evalClosure defs aty)
                | Left _ => pure (Left ("its argument " ++ show x ++ " is not flat"))
              Right (ps, rs) <- walk !(sc defs (toClosure defaultOpts Env.empty (Ref bfc Bound x)))
                | Left e => pure (Left e)
              pure (Right (LowerFlat.tys lay ++ ps, rs))
            walk res = do
              Right (_, lay) <- Flat.Translate.laidOut res
                | Left _ => pure (Left "its result is not flat")
              pure (Right ([], LowerFlat.tys lay))

            one : (Name, String, List (IRCommon.Ty enc), List (IRCommon.Ty enc)) -> Core (Maybe String)
            one (n, what, params, results) = do
              defs <- get Ctxt
              Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => pure Nothing
              let ExternDef _ = definition gdef
                | _ =>
                  pure (Just (show n ++ " is " ++ what ++ " of the native code generator, but is not declared %extern"))
              Right (ps, rs) <- walk !(nf defs Env.empty (type gdef))
                | Left e => pure (Just (show n ++ ": " ++ e))
              pure $ if ps == params && rs == results then Nothing
                     else Just (show n ++ " is declared as " ++ show ps ++ " -> " ++ show rs
                                ++ ", but the native code generator provides it as "
                                ++ show params ++ " -> " ++ show results)

        ||| Load the runtime's modules into the context: the module `Runtime`, which
        ||| imports the generic ones, the platform's module, which implements the OS
        ||| services, and the string encoding's, which nothing generic imports
        ||| either, from the installed
        ||| package, with the backend's own package, whose
        ||| heap-object model (the modules of `Compiler.Native.HeapObject`) the
        ||| runtime shares.
        loadRuntime : Platform -> HeapObject.Enc -> Core ()
        loadRuntime platform enc = do
          addPkgDir "idris2-native-runtime" anyBounds
          addPkgDir "idris2-native" anyBounds
          u <- newRef UST initUState
          traverse_ (\ns => addImport (MkImport EmptyFC False (nsAsModuleIdent ns) ns))
                    (mkNamespace "Runtime" :: toList (Linkage.OSService.platformModule platform)
                      ++ toList (Linkage.Routine.stringModule enc.string))

        ||| The foreign functions and externs of the libraries in the context, each
        ||| with how this backend implements it: by the runtime (`runtime`), by the
        ||| lowering inline (`lowered`), or not yet (`missing`). The runtime's own
        ||| externs are its inline externs and services, not the libraries', and are left
        ||| out.
        dumpForeign : HeapObject.Enc -> String -> Core ()
        dumpForeign enc path = do
          defs <- get Ctxt
          all <- traverse (\n => (n,) <$> lookupCtxtExact n (gamma defs)) !(allNames (gamma defs))
          entries <- traverse entry (mapMaybe library all)
          Right () <- coreLift
            (Data.WriteBuilder.writeBuilder path (concatMap (\e => Data.Builder.single (e ++ "\n")) (sort entries)))
            | Left err => throw (FileErr path err)
          pure ()
          where
            foreignOf : GlobalDef -> Bool
            foreignOf g = case definition g of
              ForeignDef _ _ => True
              ExternDef _ => True
              _ => False

            inRuntime : Name -> Bool
            inRuntime (NS ns _) = isPrefixOf "Runtime" (show ns)
            inRuntime _ = False

            library : (Name, Maybe GlobalDef) -> Maybe (Name, GlobalDef)
            library (n, Just g) = if foreignOf g && not (inRuntime n) then Just (n, g) else Nothing
            library (_, Nothing) = Nothing

            lowered : List String
            lowered = ["prim__newArray", "prim__arrayGet", "prim__arraySet"]

            entry : (Name, GlobalDef) -> Core String
            entry (n, _) = do
              n' <- toFullNames n
              pure $ (if elem n' (map fst (Linkage.ForeignFunctions.foreignFunctions enc)) then "runtime  "
                      else if elem (nameRoot n') lowered then "lowered  "
                      else "missing  ") ++ show n'

        ||| A phase of the compile, reported under `--timing 2` with its time and
        ||| the part of it the collector took: that part follows where collections
        ||| fall more than the phase's own work, so the rest is what the phase's
        ||| algorithms cost.
        phase : String -> Core a -> Core a
        phase name act = do
          opts <- getSession
          if not (maybe False (2 <=) (logTimings opts)) then act else do
            t0 <- coreLift (clockTime Process)
            g0 <- coreLift (clockTime GCCPU)
            res <- act
            t1 <- coreLift (clockTime Process)
            g1 <- coreLift (clockTime GCCPU)
            let collecting = case (g0, g1) of
                               (Just a, Just b) => " (collecting " ++ seconds (timeDifference b a) ++ "s)"
                               _ => ""
            coreLift_
              (putStrLn ("TIMING ++ native: " ++ name ++ ": " ++ seconds (timeDifference t1 t0) ++ "s" ++ collecting))
            pure res
          where
            seconds : Clock Duration -> String
            seconds d = let ms = toNano d `div` 1000000
                            frac = show (ms `mod` 1000)
                        in show (ms `div` 1000) ++ "." ++ pack (replicate (minus 3 (length frac)) '0') ++ frac

        ||| From VMCode to the image, under encodings whose value encoding has
        ||| fixnums: produce the term, allocate its registers, render, link.
        pipeline : (enc : HeapObject.Enc) -> {auto 0 _ : HeapObject.ValEnc.HasFixnums enc.val} ->
                   Settings -> NameMap Flat.Exp.FlatDef -> List (Name, VMDef) -> Core ELF.Image
        pipeline enc settings table defs = do
          (forms, shapes) <- phase "flat inputs" $
                               flatInputs table (Linkage.OSService.serviceBindings {enc} settings.platform)
                                          (map fst defs ++ [r.name | r <- Linkage.Routine.routines {enc}, r.provided]
                                           ++ mapMaybe (foreignRoot {enc' = enc}) defs)
          Right (_ ** term) <- phase "lowering" (later (Lower.lowerProgram enc settings.platform forms shapes defs))
            | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
          ir <- phase "register allocation" (later (RegAlloc.allocRegs X86.Target.x86_64 term))
          case settings.dumpIr of
            Just path => do
              Right () <- coreLift (Data.WriteBuilder.writeBuilder path (LocatedIR.Dump.dumpProgram ir))
                | Left err => throw (FileErr path err)
              pure ()
            Nothing => pure ()
          Right rendered <- phase "rendering" (later (X86.Render.render enc ir))
            | Left err => throw (InternalError ("native: " ++ err))
          case settings.dumpAsm of
            Just path => do
              Right () <- coreLift
                (Data.WriteBuilder.writeBuilder path
                 (concatMap (\i => Data.Builder.single (show i ++ "\n")) rendered.text))
                | Left err => throw (FileErr path err)
              pure ()
            Nothing => pure ()
          Right image <- phase "linking"
            (later (Link.linkProgram enc settings.window rendered.areas rendered.text rendered.rodata))
            | Left problems => throw (InternalError ("native: the image cannot be assembled: " ++ show problems))
          pure image
          where
            ||| Of the flat forms, those of the functions named and of the forms they
            ||| call, the functions of the OS services they call among them, and the
            ||| shapes of the data types among their types.
            flatInputs : NameMap Flat.Exp.FlatDef -> List (Name, Name) -> List Name ->
                         Core (List Flat.Exp.FlatDef, Flat.Exp.Shapes)
            flatInputs table services roots = do
              forms <- reach empty [<] roots
              let skeletons =
                    nub (filter isData (toList (concatMap (Data.Builder.piece . Flat.Exp.formSkeletons) forms)))
              shapes <- traverse (\sk => map (sk,) <$> Flat.Translate.shape sk) skeletons
              pure (forms, catMaybes shapes)
              where
                isData : Flat.Exp.Skeleton -> Bool
                isData (Flat.Exp.SCon _ _) = True
                isData _ = False

                -- the forms reached so far accumulate at their end, in the order reached
                reach : SortedMap Name () -> SnocList Flat.Exp.FlatDef -> List Name -> Core (List Flat.Exp.FlatDef)
                reach seen acc [] = pure (acc <>> [])
                reach seen acc (n :: ns) =
                  if isJust (Data.SortedMap.lookup n seen) then reach seen acc ns else do
                    Just fd <- pure (lookup n table)
                      | Nothing => reach (insert n () seen) acc ns
                    reach (insert n () seen) (acc :< fd)
                          (Flat.Exp.formCallees fd
                            ++ mapMaybe (\p => Data.List.lookup p services) (Flat.Exp.formPrims fd) ++ ns)

            ||| A pure computation as an action, so that it runs where the action runs:
            ||| inside `phase`.
            later : Lazy a -> Core a
            later x = coreLift (primIO (\w => MkIORes (force x) w))

            ||| The runtime's function for a foreign function of the program it
            ||| implements.
            foreignRoot : {enc' : HeapObject.Enc} -> (Name, VMDef) -> Maybe Name
            foreignRoot (n, MkVMForeign {}) = lookup n (Linkage.ForeignFunctions.foreignFunctions enc')
            foreignRoot _ = Nothing

    executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                  (tmpDir : String) -> ClosedTerm -> Core ()
    executeExpr c s tmpDir tm = do
      Just exe <- compileExpr c s tmpDir tmpDir tm "_tmp_native"
        | Nothing => throw (InternalError "native: compilation failed")
      coreLift_ $ system [exe]
