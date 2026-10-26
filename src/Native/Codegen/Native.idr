||| The native backend: `--cg native` pulls VMCode and the flat forms of the
||| functions the program marks flat (`Flat.Marked`) and of what they call,
||| with the shapes of the types they handle (`Flat.Translate.shape`),
||| lowers them to the typed term and through it to
||| the IR, registers allocated and live lists computed
||| (`Native.Codegen.Lower`), renders it as x86-64 instructions
||| (`Native.Codegen.X86.Render`) and links them with the runtime seed into
||| a static ELF (x86-64 Linux). What the lowering does not cover yet is the
||| seed's abort stub, so a program always links and fails with status 70
||| only on the paths that reach it.
|||
||| The runtime is a library of flat functions, the package
||| `idris2-native-runtime`, which a program does not import: the backend
||| loads its modules into the context itself, and its routines, those the
||| runtime contract names (`routines` in `Native.Codegen.Linkage.Routine`), are
||| compiled into every program with the program's own forms.
module Native.Codegen.Native

import Native.Codegen.ELF
import Native.Codegen.Evaluate
import Native.Codegen.Link
import Native.Codegen.Linkage.Areas as Linkage
import Native.Codegen.Linkage.ForeignFunctions
import Native.Codegen.Linkage.OSService
import Native.Codegen.Linkage.Realised as Linkage
import Native.Codegen.Linkage.Routine
import Native.Codegen.Linkage.RuntimeModule
import Native.Codegen.Linkage.Sym as Linkage
import Native.Codegen.Linkage.SystemLibrary as Linkage
import Native.Codegen.LocatedIR.Dump
import Native.Codegen.LocatedIR.Program as LocatedIR
import Native.Codegen.LocatedIR.Reach
import Native.Codegen.Lower
import Native.Codegen.Platform
import Native.Codegen.RegAlloc
import Native.Codegen.Tabulate
import Native.Codegen.TermIR.Decls as TermIR
import Native.Codegen.TermIR.Program as TermIR
import Native.Codegen.X86.Asm
import Native.Codegen.X86.Encode
import Native.Codegen.X86.Render
import Native.Codegen.X86.Target

import Compiler.Common
import Compiler.VMCode
import Core.CompileExpr
import Core.Context
import Core.Context.Context
import Core.Core
import Core.Directory
import Core.Env
import Core.FC
import Core.Name
import Core.Name.Namespace
import Core.Name.Scoped
import Core.Normalise
import Core.Normalise.Convert
import Core.Options
import Core.TT
import Core.TT.Term
import Core.UnifyState
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.String
import Idris.Package.Types
import Idris.ProcessIdr
import Idris.SetOptions
import Idris.Syntax
import Libraries.Data.NameMap
import Libraries.Utils.Path
import Native.Data.Builder as Data
import Native.Data.WriteBuilder
import Native.Flat.Exp
import Native.Flat.Marked
import Native.Flat.Translate
import Native.HeapObj.ValEnc
import Native.Intrinsic
import Native.Types.BignumEnc as Types
import Native.Types.Enc as Types
import Native.Types.StringEnc as Types
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
||| * `static <name>...`: the constants the program marks static
|||   (`Flat.Marked`). A mark of what is no constant, of a constant Idris
|||   inlines at each use or that is marked flat too, or of one the program
|||   reaches whose value the evaluation as the program is compiled does not
|||   compute (`Native.Codegen.Evaluate`), is refused, with why
|||   (`checkStaticConstants`). The program computes each on its first use
|||   still, as any constant.
||| * `dump-flat=<file>`: write the flat forms, and the shapes of their data
|||   types, to the file.
||| * `dump-ir=<file>`: write the IR the produce pass makes to the file.
||| * `dump-asm=<file>`: write the rendered instructions to the file, in Intel
|||   syntax, with each function's name before its code.
||| * `dump-foreign=<file>`: write the foreign functions and externs of the
|||   program's libraries, each with how this backend implements it.
||| * `val-encoding=tag1`, `tag0` or `nofixnums`: how a uniform value is a word
|||   (`HeapObj.ValEnc`): fixnum tag 1, the default; fixnum tag 0; or no
|||   fixnums, every integer boxed, which is not implemented yet and so is
|||   refused.
||| * `string-encoding=utf8` or `utf32`: how a `String` is laid out
|||   (`StringEnc`): UTF-8 with the ASCII bit, the default, or UTF-32,
|||   which is not implemented yet and so is refused.
||| * `target=<arch>-<os>`: the platform the program is compiled for
|||   (`Native.Codegen.Platform`), `x86_64-linux` by default; one not built
|||   yet is refused by name.
record Settings where
  constructor MkSettings
  window : Int
  dumpFlat : Maybe String
  dumpIr : Maybe String
  dumpAsm : Maybe String
  dumpForeign : Maybe String
  encodings : Types.Enc
  platform : Platform
  system : Linkage.SystemLibrary

export
codegenNative : Codegen
codegenNative = MkCG compileExpr executeExpr Nothing Nothing
  where
    ||| The most steps an evaluation when the program is compiled takes to
    ||| compute one value, a table's row or a constant, one marked static or
    ||| one either reads, which is computed once, in steps of its own
    ||| (`Native.Codegen.Evaluate`). Each step is a call, a case, an
    ||| operation or a word made: a bound on the work of each value, but for
    ||| what one step costs as its values grow, such as an operation on a
    ||| long string. A value that needs more is not computed, an error, and
    ||| never computed some other way.
    evaluationFuel : Nat
    evaluationFuel = 100000000

    compileExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                  (tmpDir : String) -> (outputDir : String) ->
                  ClosedTerm -> (outfile : String) -> Core (Maybe String)
    compileExpr c s _ outputDir tm outfile = do
      Right settings <- parseSettings <$> getDirectives Flat.Marked.markingCG
        | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
      Just marked <- phase "the runtime loaded"
        (Flat.Marked.markedForms Linkage.Realised.flatPrimitives
          (loadRuntime settings.platform settings.encodings settings.system))
        | Nothing => pure Nothing
      Right realised <- phase "the contract realised"
        (Linkage.Realised.realise settings.platform settings.encodings)
        | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
      whenJust settings.dumpFlat $ \f => dumpFlat f marked.forms
      whenJust settings.dumpForeign $ \f => dumpForeign settings realised f
      -- the compiled forms of the tables and of the constants marked
      -- static, and of all they call, which Idris's passes, from `main`,
      -- may not reach: a table only the runtime's flat code reads, and a
      -- mark the program does not reach, which is checked all the same
      earlyForms <- phase "the tables and static constants compiled"
        (Evaluate.compileFor (keys realised.tables ++ marked.staticConstants))
      -- the foreign functions the program reaches, each with the runtime's
      -- function that implements it: the flat ones, and the ordinary ones,
      -- which Idris compiles with the program
      (flat, bound) <- phase "the foreign functions bound" (bindForeign settings marked.forms tm)
      cdata <- phase "Idris's passes" (withSystem bound tm)
      -- the compiled form of each definition of the program, as Idris gives
      -- it to every code generator, and the tables' and the static
      -- constants': what they are computed from
      let compiled = mergeLeft (fromList (map (\(n, _, d) => (n, d)) cdata.namedDefs)) earlyForms
      phase "the static constants evaluated"
        (checkStaticConstants (realisedMeanings realised) compiled marked.flatFunctions
          (filter (\n => any ((== n) . fst) (vmcode cdata)) marked.staticConstants)
          marked.staticConstants)
      -- the definitions evaluated once, on their first use: every one of
      -- no arguments but the entry. The Scheme backends, which evaluate
      -- them before `main`, leave out those whose evaluation may crash or
      -- recur, which on first use crash or recur as they would unshared
      let constants = mapMaybe kept (vmcode cdata)
      image <- case settings.encodings of
        Types.MkEnc HeapObj.ValEnc.FixnumTag1 b s =>
          pipeline (Types.MkEnc HeapObj.ValEnc.FixnumTag1 b s) settings realised marked.forms
            compiled constants flat bound (vmcode cdata)
        Types.MkEnc HeapObj.ValEnc.FixnumTag0 b s =>
          pipeline (Types.MkEnc HeapObj.ValEnc.FixnumTag0 b s) settings realised marked.forms
            compiled constants flat bound (vmcode cdata)
        Types.MkEnc HeapObj.ValEnc.NoFixnums _ _ =>
          throw (GenericMsg EmptyFC "native: the encoding nofixnums is not implemented")
      coreLift_ $ mkdirAll outputDir
      let outexec = outputDir </> outfile
      Right () <- phase "the image written" (coreLift (ELF.writeImage outexec image))
        | Left err => throw (FileErr outexec err)
      pure (Just outexec)
      where
        ||| The foreign functions the program's term reaches that the runtime
        ||| implements, each with the first of its candidates the loaded runtime
        ||| defines (`ForeignFunctions.candidates`): those a flat function
        ||| implements, and those an ordinary one does, each checked to be of
        ||| its foreign function's type. A foreign function an ordinary
        ||| implementation reaches is reached too.
        bindForeign : Settings -> NameMap Flat.Exp.FlatDef -> ClosedTerm ->
                      Core (List (Name, Name), List (Name, Name))
        bindForeign settings table tm = do
          defs <- get Ctxt
          (flat, ordinary) <- reach defs empty [] [] (keys (getRefs (Resolved (-1)) tm))
          traverse_ (agree defs) ordinary
          pure (flat, ordinary)
          where
            -- the first candidate the context defines
            implementer : Defs -> Name -> Core (Maybe Name)
            implementer defs f = firstDefined
              (Linkage.ForeignFunctions.candidates settings.encodings settings.system f)
              where
                firstDefined : List Name -> Core (Maybe Name)
                firstDefined [] = pure Nothing
                firstDefined (c :: cs) = do
                  Just _ <- lookupCtxtExact c (gamma defs)
                    | Nothing => firstDefined cs
                  pure (Just c)

            -- the foreign functions the names reach, those found so far among
            -- the definitions seen so far
            covering
            reach : Defs -> NameMap () -> (flat, ordinary : List (Name, Name)) -> List Name ->
                    Core (List (Name, Name), List (Name, Name))
            reach defs seen flat ordinary [] = pure (flat, ordinary)
            reach defs seen flat ordinary (n :: ns) = do
              full <- toFullNames n
              if isJust (lookup full seen) then reach defs seen flat ordinary ns else do
                let seen' = insert full () seen
                Just gdef <- lookupCtxtExact full (gamma defs)
                  | Nothing => reach defs seen' flat ordinary ns
                let refs = keys (refersToRuntime gdef)
                case definition gdef of
                  ForeignDef _ _ => do
                    impl <- implementer defs full
                    case impl of
                      Just i =>
                        if isJust (lookup i table)
                          then reach defs seen' ((full, i) :: flat) ordinary ns
                          else reach defs seen' flat ((full, i) :: ordinary) (i :: ns)
                      Nothing => reach defs seen' flat ordinary ns
                  _ => reach defs seen' flat ordinary (refs ++ ns)

            -- an implementation of its foreign function's type, or the reason:
            -- both normalised with every name visible, so that an alias
            -- `base` keeps private (`System.File.Meta.FileTimePtr`, an
            -- `AnyPtr`) is the type it names
            agree : Defs -> (Name, Name) -> Core ()
            agree defs (f, impl) = do
              Just fdef <- lookupCtxtExact f (gamma defs)
                | Nothing => throw (UndefinedName EmptyFC f)
              Just idef <- lookupCtxtExact impl (gamma defs)
                | Nothing =>
                    throw (GenericMsg EmptyFC
                      ("native: the runtime has no " ++ show impl ++ ", which implements "
                       ++ show f))
              fty <- normaliseAll defs Env.empty fdef.type
              ity <- normaliseAll defs Env.empty idef.type
              True <- convert defs Env.empty fty ity
                | False =>
                    throw (GenericMsg EmptyFC
                      ("native: " ++ show impl ++ " is not of the type of " ++ show f
                       ++ ", which it implements"))
              pure ()

        ||| Idris's passes over the program's term, which compile the
        ||| implementations with it: each given to them as a function the
        ||| backend exports, which they compile whatever the program reaches,
        ||| for these passes alone.
        withSystem : List (Name, Name) -> ClosedTerm -> Core CompileData
        withSystem bound tm = do
          defs <- get Ctxt
          let exports = defs.foreignExports
          put Ctxt
            ({ foreignExports :=
                 foldl (\m, (_, impl) => insert impl [(systemExports, show impl)] m) exports bound }
               defs)
          cdata <- getCompileDataWith [systemExports] False VMCode tm
          update Ctxt { foreignExports := exports }
          pure cdata
          where
            -- the backend the implementations are exported for
            systemExports : String
            systemExports = "native-system"

        ||| What the evaluation takes the realised makers and primitives to
        ||| mean (`Evaluate.Meanings`).
        realisedMeanings : Linkage.Realised -> Evaluate.Meanings
        realisedMeanings realised = Evaluate.MkMeanings realised.makers realised.primitives

        ||| The constants the program marks static, each checked now to be a
        ||| definition of no arguments, which no directive marks flat too,
        ||| and which Idris does not inline at each use: one it inlines has no
        ||| use left for the program's compilation to reach, so every mark is
        ||| checked, reached or not. Each the compilation reaches is
        ||| evaluated now too, over the compiled definitions, in at most
        ||| `evaluationFuel` steps of its own, whatever the order of the
        ||| marks, and its value must be computed. Every one that fails ends
        ||| the compilation, in one error that says why of each, in the order
        ||| of the marks.
        checkStaticConstants : Evaluate.Meanings -> (compiled : SortedMap Name NamedDef) ->
                               (flatFunctions, reached, marks : List Name) -> Core ()
        checkStaticConstants meanings compiled flatFunctions reached marks = do
          defs <- get Ctxt
          refused <- catMaybes <$> traverse (refusal defs) marks
          values <- Evaluate.constants meanings compiled evaluationFuel
                      (filter (\n => isNothing (lookup n refused)) reached)
          let failures = refused ++ mapMaybe (\(n, v) => (n,) <$> either Just (const Nothing) v)
                                               values
          let [] = mapMaybe (\n => (n,) <$> lookup n failures) marks
            | failed =>
              throw (GenericMsg EmptyFC
                ("native: refused as static constants:"
                 ++ concatMap (\(n, why) => "\n  " ++ show n ++ " is " ++ why) failed))
          pure ()
          where
            -- why a constant marked static is refused before it is
            -- evaluated, if it is
            refusal : Defs -> Name -> Core (Maybe (Name, String))
            refusal defs n = do
              g <- lookupCtxtExact n (gamma defs)
              -- what stops Idris inlining it, if Idris does
              let fix = g >>= \g' => toMaybe (Evaluate.inlined g') (Evaluate.inliningFix g')
              pure $ (n,) <$>
                if elem n flatFunctions
                  then Just "marked flat too: a function is flat, or a constant static, not both"
                else case fix of
                  Just f => Just ("inlined by Idris at each use, so no use would read it: " ++ f)
                  Nothing => case lookup n compiled of
                    Just (MkNmFun [] _) => Nothing
                    Just (MkNmFun [_] _) => Just "a function of 1 argument, not a constant"
                    Just (MkNmFun ps _) =>
                      Just ("a function of " ++ show (length ps) ++ " arguments, not a constant")
                    Just (MkNmError _) => Nothing
                    Just (MkNmCon {}) => Just "a constructor, not a constant"
                    Just (MkNmForeign {}) => Just "a foreign function, not a constant"
                    Nothing => Just "a definition the program does not compile"

        -- a function of no arguments, but the entry, which runs once
        kept : (Name, VMDef) -> Maybe Name
        kept (n, MkVMFun [] _) = if n /= Lower.mainExpression then Just n else Nothing
        kept _ = Nothing

        parseSettings : List String -> Either String Settings
        parseSettings =
          foldlM setting
            (MkSettings Link.windowBytes Nothing Nothing Nothing Nothing Types.Enc.defaultEnc
             Platform.defaultPlatform Linkage.SystemLibrary.NativeSystem)
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
              ["val-encoding", "tag1"] => Right ({ encodings.val := HeapObj.ValEnc.FixnumTag1 } o)
              ["val-encoding", "tag0"] => Right ({ encodings.val := HeapObj.ValEnc.FixnumTag0 } o)
              ["val-encoding", "nofixnums"] =>
                Left "the encoding nofixnums, every integer boxed, is not implemented"
              ["val-encoding", v] =>
                Left ("val-encoding= takes tag1, tag0 or nofixnums, not " ++ show v)
              ["string-encoding", "utf8"] => Right ({ encodings.string := Types.StringEnc.Utf8 } o)
              ["string-encoding", "utf32"] => Left "the string encoding utf32 is not implemented"
              ["string-encoding", v] =>
                Left ("string-encoding= takes utf8 or utf32, not " ++ show v)
              ["system", v] => case Linkage.SystemLibrary.parseSystemLibrary v of
                Just l => Right ({ system := l } o)
                Nothing => Left ("system= takes native, not " ++ show v)
              ["target", v] => case Platform.parsePlatform v of
                Just p => if Platform.built p then Right ({ platform := p } o)
                          else Left
                            ("the target " ++ show p ++ " is not implemented; only x86_64-linux is")
                Nothing => Left ("target= takes <arch>-<os>, such as x86_64-linux, not " ++ show v)
              _ => Right o

        ||| Load the runtime's modules into the context: the roots of its core, of
        ||| its support tier and of the system library's, which import the
        ||| generic ones, the platform's module, which implements the OS
        ||| services, and the string encoding's and the bignum encoding's,
        ||| which nothing generic imports either, from the installed package,
        ||| with the backend's own package, whose heap-object model and type
        ||| layer (the modules of `HeapObj` and `Types`) the runtime shares.
        loadRuntime : Platform -> Types.Enc -> Linkage.SystemLibrary -> Core ()
        loadRuntime platform enc lib = do
          addPkgDir "idris2-native-runtime" anyBounds
          addPkgDir "idris2-native" anyBounds
          u <- newRef UST initUState
          traverse_ (\ns => addImport (MkImport EmptyFC False (nsAsModuleIdent ns) ns))
                    (Linkage.RuntimeModule.runtimeModule ""
                      :: Linkage.RuntimeModule.supportModule ""
                      :: Linkage.RuntimeModule.systemModule lib ""
                      :: toList (Linkage.OSService.platformModule platform)
                      ++ toList (Linkage.RuntimeModule.stringModule enc.string)
                      ++ toList (Linkage.RuntimeModule.bignumModule enc))

        ||| The foreign functions and externs of the libraries in the context, each
        ||| with how this backend implements it: by the runtime (`runtime`), by the
        ||| lowering inline (`lowered`), or not yet (`missing`). The contract's
        ||| externs, the inline externs and the services' (`realised`), are not
        ||| the libraries', and are left out, as is anything of the runtime's.
        dumpForeign : Settings -> Linkage.Realised -> String -> Core ()
        dumpForeign settings realised path = do
          defs <- get Ctxt
          all <- traverse (\n => (n,) <$> lookupCtxtExact n (gamma defs)) !(allNames (gamma defs))
          entries <- traverse (entry defs) (mapMaybe library all)
          Right () <- coreLift
            (Data.WriteBuilder.writeBuilder path
              (concatMap (\e => Data.Builder.single (e ++ "\n")) (sort entries)))
            | Left err => throw (FileErr path err)
          pure ()
          where
            isForeign : GlobalDef -> Bool
            isForeign g = case definition g of
              ForeignDef _ _ => True
              ExternDef _ => True
              _ => False

            inRuntime : Name -> Bool
            inRuntime (NS ns _) = Linkage.RuntimeModule.inRuntime ns
            inRuntime _ = False

            contract : Name -> Bool
            contract n = isJust (lookup n realised.externs) || isJust (lookup n realised.services)

            library : (Name, Maybe GlobalDef) -> Maybe (Name, GlobalDef)
            library (n, Just g) = if isForeign g && not (inRuntime n || contract n) then Just (n, g)
              else Nothing
            library (_, Nothing) = Nothing

            lowered : List String
            lowered =
              ["prim__newArray", "prim__arrayGet", "prim__arraySet", "prim__newIORef",
               "prim__readIORef", "prim__writeIORef", "prim__os", "prim__codegen"]

            -- whether the runtime defines one of the foreign function's candidates
            implemented : Defs -> Name -> Core Bool
            implemented defs n =
              anyM (\c => isJust <$> lookupCtxtExact c (gamma defs))
                (Linkage.ForeignFunctions.candidates settings.encodings settings.system n)
              where
                anyM : (Name -> Core Bool) -> List Name -> Core Bool
                anyM p [] = pure False
                anyM p (x :: xs) = if !(p x) then pure True else anyM p xs

            entry : Defs -> (Name, GlobalDef) -> Core String
            entry defs (n, _) = do
              n' <- toFullNames n
              runtime <- implemented defs n'
              pure $
                (if runtime then "runtime  "
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
                               (Just a, Just b) => " (collecting " ++ seconds (timeDifference b a)
                                 ++ "s)"
                               _ => ""
            coreLift_
              (putStrLn
                ("TIMING ++ native: " ++ name ++ ": " ++ seconds (timeDifference t1 t0) ++ "s"
                 ++ collecting))
            pure res
          where
            seconds : Clock Duration -> String
            seconds d = let ms = toNano d `div` 1000000
                            frac = show (ms `mod` 1000)
                        in show (ms `div` 1000) ++ "."
                          ++ pack (replicate (minus 3 (length frac)) '0') ++ frac

        ||| From VMCode to the image, under encodings whose value encoding has
        ||| fixnums: produce the term, allocate its registers, render, link.
        pipeline : (enc : Types.Enc) -> {auto 0 _ : HeapObj.ValEnc.HasFixnums enc.val} ->
                   Settings -> Linkage.Realised -> NameMap Flat.Exp.FlatDef ->
                   (compiled : SortedMap Name NamedDef) -> (constants : List Name) ->
                   (flat, bound : List (Name, Name)) -> List (Name, VMDef) -> Core ELF.Image
        pipeline enc settings realised table compiled constants flat bound defs = do
          (forms, shapes) <- phase "flat inputs" $
                               flatInputs table (Data.SortedMap.toList realised.services)
                                          (map fst defs
                                            ++
                                              [r.name
                                               | r <- Linkage.Routine.routines {enc} realised]
                                           ++ map snd flat)
          -- each table's row, by its first: the lowering's reads of it
          firsts <- phase "table rows"
            (traverse (\(n, (lo, _)) => tabulated (n, (lo, lo))) (reached forms))
          let tables = fromList [ (t.name, (t.lo, t.rowWords)) | t <- firsts ]
          Right (_ ** term) <- phase "lowering"
            (later
              (Lower.lowerProgram enc settings.platform realised forms shapes tables constants
                 flat bound defs))
            | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
          allocated <- phase "register allocation"
            (later (RegAlloc.allocRegs X86.Target.x86_64 term))
          -- the image holds what the entry and the routines the seed reaches
          -- by symbol reach, and the tables of that alone
          let (ir, readTables) =
                LocatedIR.Reach.reach
                  (\n => isJust (Linkage.Routine.routineSymbol {enc} realised n)) allocated
          rows <- phase "tables"
            (traverse tabulated (mapMaybe (\n => (n,) <$> lookup n realised.tables) readTables))
          case settings.dumpIr of
            Just path => do
              Right () <- coreLift
                (Data.WriteBuilder.writeBuilder path (LocatedIR.Dump.dumpProgram ir))
                | Left err => throw (FileErr path err)
              pure ()
            Nothing => pure ()
          Right rendered <- phase "rendering"
            (later (X86.Render.render enc realised (map (\t => (t.name, t.bytes)) rows) ir))
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
            (later
              (Link.linkProgram enc settings.window
                 ({ constants := 2 * length constants } rendered.areas) rendered.text
                 rendered.rodata))
            | Left problems =>
              throw (InternalError ("native: the image cannot be assembled: " ++ show problems))
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
                    nub
                      (filter isData
                       (toList (concatMap (Data.Builder.piece . Flat.Exp.formSkeletons) forms)))
              shapes <- traverse (\sk => map (sk,) <$> Flat.Translate.shape sk) skeletons
              pure (forms, catMaybes shapes)
              where
                isData : Flat.Exp.Skeleton -> Bool
                isData (Flat.Exp.SCon _ _) = True
                isData _ = False

                -- the forms reached so far accumulate at their end, in the order reached
                reach : SortedMap Name () -> SnocList Flat.Exp.FlatDef -> List Name ->
                        Core (List Flat.Exp.FlatDef)
                reach seen acc [] = pure (acc <>> [])
                reach seen acc (n :: ns) =
                  if isJust (Data.SortedMap.lookup n seen) then reach seen acc ns else do
                    Just fd <- pure (lookup n table)
                      | Nothing => reach (insert n () seen) acc ns
                    reach (insert n () seen) (acc :< fd)
                          (Flat.Exp.formCallees fd
                            ++ mapMaybe (\p => Data.List.lookup p services) (Flat.Exp.formPrims fd)
                              ++ ns)

            ||| The tables the forms reach, with their ranges.
            reached : List Flat.Exp.FlatDef -> List (Name, (Int, Int))
            reached fs =
              nub
                (mapMaybe (\n => (n,) <$> lookup n realised.tables)
                 (concatMap Flat.Exp.formPrims fs))

            ||| A table's rows, computed now (`Native.Codegen.Tabulate`).
            tabulated : (Name, (Int, Int)) -> Core Tabulate.Tabulated
            tabulated (n, (lo, hi)) = do
              Right t <-
                Tabulate.tabulate (realisedMeanings realised) compiled evaluationFuel n lo hi
                | Left err => throw (GenericMsg EmptyFC ("native: " ++ err))
              pure t

            ||| A pure computation as an action, so that it runs where the action runs:
            ||| inside `phase`.
            later : Lazy a -> Core a
            later x = coreLift (primIO (\w => MkIORes (force x) w))

            ||| The runtime's function for a foreign function of the program it
            ||| implements.

    executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
                  (tmpDir : String) -> ClosedTerm -> Core ()
    executeExpr c s tmpDir tm = do
      Just exe <- compileExpr c s tmpDir tmpDir tm "_tmp_native"
        | Nothing => throw (InternalError "native: compilation failed")
      coreLift_ $ system [exe]
