||| What a program reaches of the flat forms and of the constants marked
||| static (`programReach`): the forms the code generator lowers with the
||| program, and the marks it evaluates as it compiles it. A form no root
||| of the program leads to is not lowered, so the marks only it reads are
||| not evaluated, and a routine of the runtime whose form is not among
||| those reached is declared outside the program, so that a call of it
||| stops the compile (`Native.Codegen.Lower.lowerProgram`).
module Native.Codegen.ProgramReach

import Core.Name
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Libraries.Data.NameMap
import Native.Flat.Exp

%default total

||| What a program reaches (`programReach`).
public export
record ProgramReach where
  constructor MkProgramReach
  ||| The forms reached, in the order of the walk from every routine.
  forms : List Flat.Exp.FlatDef
  ||| The marks reached, in the marks' order.
  marks : List Name

||| What the program reaches of the flat forms (`table`, by the names of
||| their functions) and of the constants marked static (`marks`).
|||
||| A form is reached from a root, and from a form reached through the
||| forms it calls (`Flat.Exp.formCallees`) and the functions its
||| primitives are bound to (`Flat.Exp.formPrims`, by `services`: the OS
||| services' and the string encoding's text externs'). The roots are
||| every function of the program's VMCode (`functions`), which Idris's
||| passes have cut to what `main` and the exports reach; the routines of
||| the runtime that are roots (`routines`: each routine, in the
||| contract's order, with whether it is one, which it is when the seed
||| reaches it by its symbol or the lowering of VMCode may call it); and
||| the flat functions that implement its foreign functions
||| (`implementations`). A routine that is not a root is reached all the
||| same when a form reached leads to it. A mark is reached if VMCode has
||| it, or a form reached reads it (`Flat.Exp.formStatics`).
|||
||| A form keeps its place whichever routines the program reaches: the
||| forms reached come in the order of the walk from every routine, the
||| functions of VMCode before them and the implementations after, so that
||| a program's image holds its functions in one order however few of the
||| runtime's it reaches. Of VMCode's functions, the walks start from
||| those that have a form alone (`formed`): a name without one leads
||| nowhere, and most have none, so a walk need not meet them. Covering,
||| not total, only because the forms' calls, primitives and reads are
||| found by covering functions; the walk itself ends (`walk`).
export covering
programReach : (table : NameMap Flat.Exp.FlatDef) -> (services : SortedMap Name Name) ->
               (functions : List Name) -> (routines : List (Name, Bool)) ->
               (implementations, marks : List Name) -> ProgramReach
programReach table services functions routines implementations marks =
  let fuel = foldlNames (\k, _, _ => S k) Z table
      formed = filter hasForm functions
      reached = names (walked fuel (formed ++ map fst (filter snd routines) ++ implementations))
      forms = filter (isIn reached) (walked fuel (formed ++ map fst routines ++ implementations))
      -- the sets each mark is tested against, bound here so that they are
      -- built once, not again for each mark
      vm = among (Data.SortedSet.fromList marks) functions
      read = reads forms
  in MkProgramReach forms (filter (isReached vm read) marks)
  where
    ||| Whether the function has a form.
    hasForm : Name -> Bool
    hasForm n = isJust (lookup n table)

    ||| The names a form leads to: the forms it calls, then the functions
    ||| of the services among its primitives.
    next : Flat.Exp.FlatDef -> List Name
    next fd = Flat.Exp.formCallees fd
                ++ mapMaybe (\p => lookup p services) (Flat.Exp.formPrims fd)

    ||| The forms the roots lead to, each once, in the order a walk depth
    ||| first meets them: a name's form (`form`), then the names it leads to
    ||| (`leads`), before the names after it. A name without a form leads
    ||| nowhere. Each form met takes one of the fuel, so the fuel ends the
    ||| walk, and as much as there are forms is enough.
    total
    walk : (form : Name -> Maybe Flat.Exp.FlatDef) -> (leads : Flat.Exp.FlatDef -> List Name) ->
           (fuel : Nat) -> (roots : List Name) -> List Flat.Exp.FlatDef
    walk form leads fuel roots = go fuel empty [<] roots
      where
        go : Nat -> SortedSet Name -> SnocList Flat.Exp.FlatDef -> List Name ->
             List Flat.Exp.FlatDef
        go _ seen acc [] = acc <>> []
        go Z seen acc (_ :: _) = acc <>> []
        go (S k) seen acc (n :: ns) =
          if contains n seen then go (S k) seen acc ns else
            case form n of
              Nothing => go (S k) (insert n seen) acc ns
              Just fd => go k (insert n seen) (acc :< fd) (leads fd ++ ns)

    ||| The forms the roots lead to, in the order the walk meets them.
    walked : Nat -> List Name -> List Flat.Exp.FlatDef
    walked fuel = walk (\n => lookup n table) next fuel

    ||| The names of the forms' functions.
    names : List Flat.Exp.FlatDef -> SortedSet Name
    names = foldl (\s, fd => insert fd.name s) empty

    ||| Whether the form is among those reached.
    isIn : SortedSet Name -> Flat.Exp.FlatDef -> Bool
    isIn reached fd = contains fd.name reached

    ||| The names that are among those of the set (`wanted`), as a set: of
    ||| VMCode's functions, the marks it has. The set tested against is the
    ||| marks', which are few; VMCode's functions, which are many, are each
    ||| tested once and not made a set themselves.
    among : (wanted : SortedSet Name) -> List Name -> SortedSet Name
    among wanted = foldl (\s, n => if contains n wanted then insert n s else s) empty

    ||| The marks the forms read.
    reads : List Flat.Exp.FlatDef -> SortedSet Name
    reads = foldl (\s, fd => foldl (\s', r => insert (fst r) s') s (Flat.Exp.formStatics fd)) empty

    ||| Whether a mark is reached: VMCode has it (`vm`, of the marks those it
    ||| has) or a form reached reads it (`read`).
    isReached : (vm, read : SortedSet Name) -> Name -> Bool
    isReached vm read m = contains m vm || contains m read
