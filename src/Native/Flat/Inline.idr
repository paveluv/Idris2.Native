||| Small flat forms inlined where flat code calls them (`inlineSmall`).
|||
||| A form is *small* when its body calls no form and has at most
||| `smallNodes` nodes: an `Ord Bits64` comparison, which is the primitive
||| comparison and a case that gives `False` or `True`, or a pair's
||| projection, a case that gives a field. A call of a small form is
||| replaced by its body: each argument bound in turn to a fresh copy of the
||| parameter it is passed for, then the body with its parameters renamed to
||| them. The arguments are evaluated in the call's order and the body after
||| them, as the call would, and a form is closed over its parameters, so
||| the body refers to nothing of the caller's. A body inlined into another
||| keeps its own binders: flat scopes are lexical, so one of them can only
||| hide a name inside the body itself.
|||
||| Callers are inlined after their callees, by a walk of the calls in
||| depth, so a form that calls only small ones may become small in turn. A
||| form in a cycle of calls calls one of the cycle, so it is never small,
||| and inlining ends. The caller decides with `mayInline` which small forms
||| it may take: the runtime's memory module alone may convert between words
||| and addresses, so its forms are inlined only into its own.
module Native.Flat.Inline

import Native.Flat.Exp

import Core.FC
import Core.Name
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.Vect
import Data.Zippable
import Libraries.Data.NameMap
import Native.Data.Stateful as Data

%default covering

||| What the walk has made: each form done, its body with the small forms it
||| calls inlined; the small ones among them; the forms being walked; the
||| next fresh name's number.
record Walk where
  constructor MkWalk
  done : NameMap Exp.FlatDef
  small : NameMap Exp.FlatDef
  walking : NameMap ()
  nextName : Int

M : Type -> Type
M = Data.Stateful Walk Void

parameters (table : NameMap Exp.FlatDef) (mayInline : (caller, callee : Name) -> Bool)
  mutual
    ||| The form, and before it every form it calls, walked: its body with the
    ||| small forms it calls inlined, recorded as done, and as small if it is.
    walk : Name -> M ()
    walk f = do
      w <- Data.Stateful.get
      case (NameMap.lookup f w.done, NameMap.lookup f w.walking, NameMap.lookup f table) of
        (Nothing, Nothing, Just d) => do
          Data.Stateful.put ({ walking $= NameMap.insert f () } w)
          traverse_ walk (callees d.body [])
          body <- inlined f d.body
          let d' = { body := body } d
          Data.Stateful.modify
            { done $= NameMap.insert f d',
              small $= (if isJust (leafWithin smallNodes body) then NameMap.insert f d' else id),
              walking $= NameMap.delete f }
        _ => pure ()
      where
        ||| The most nodes a small form's body has: a comparison has eight, a
        ||| projection three.
        smallNodes : Nat
        smallNodes = 16

        ||| The nodes left of `budget` once the expression's are counted, if it calls
        ||| no form and has no more than `budget` of them.
        leafWithin : (budget : Nat) -> Exp -> Maybe Nat
        leafWithin Z _ = Nothing
        leafWithin (S n) e = case e of
          Exp.FVar _ _ => Just n
          Exp.FLet _ _ val sc => leafWithin n val >>= \m => leafWithin m sc
          Exp.FConst _ _ => Just n
          Exp.FOp _ _ as => all n (toList as)
          Exp.FCall _ _ _ => Nothing
          Exp.FPrim _ _ _ _ as => all n as
          Exp.FStatic _ _ _ _ => Just n
          Exp.FCon _ _ _ _ _ as => all n as
          Exp.FCase _ sc alts dflt => do
                m <- leafWithin n sc
                k <- alternatives m alts
                maybe (Just k) (leafWithin k) dflt
          Exp.FCrash _ _ => Just n
          Exp.FNone _ => Just n
          where
            all : Nat -> List Exp -> Maybe Nat
            all n [] = Just n
            all n (x :: xs) = leafWithin n x >>= \m => all m xs

            alternatives : Nat -> List Exp.FlatAlt -> Maybe Nat
            alternatives n [] = Just n
            alternatives n (Exp.FConAlt _ _ _ sc :: as) = leafWithin n sc >>= \m =>
              alternatives m as
            alternatives n (Exp.FConstAlt _ sc :: as) = leafWithin n sc >>= \m => alternatives m as

        ||| The forms the expression calls, before `acc`.
        callees : Exp -> (acc : List Name) -> List Name
        callees e acc = case e of
          Exp.FVar _ _ => acc
          Exp.FLet _ _ val sc => callees val (callees sc acc)
          Exp.FConst _ _ => acc
          Exp.FOp _ _ as => all (toList as) acc
          Exp.FCall _ n as => n :: all as acc
          Exp.FPrim _ _ _ _ as => all as acc
          Exp.FStatic _ _ _ _ => acc
          Exp.FCon _ _ _ _ _ as => all as acc
          Exp.FCase _ sc alts dflt =>
            callees sc (alternatives alts (maybe acc (\d => callees d acc) dflt))
          Exp.FCrash _ _ => acc
          Exp.FNone _ => acc
          where
            all : List Exp -> List Name -> List Name
            all xs acc = foldr callees acc xs

            alternatives : List Exp.FlatAlt -> List Name -> List Name
            alternatives [] acc = acc
            alternatives (Exp.FConAlt _ _ _ sc :: as) acc = callees sc (alternatives as acc)
            alternatives (Exp.FConstAlt _ sc :: as) acc = callees sc (alternatives as acc)

    ||| The expression in `caller`, with each call of a small form it may take
    ||| replaced by the form's body.
    inlined : (caller : Name) -> Exp -> M Exp
    inlined caller e = case e of
      Exp.FVar _ _ => pure e
      Exp.FLet fc v val sc =>
        [| Exp.FLet (pure fc) (pure v) (inlined caller val) (inlined caller sc) |]
      Exp.FConst _ _ => pure e
      Exp.FOp fc op as => Exp.FOp fc op <$> traverse (inlined caller) as
      Exp.FCall fc g as => do
            as' <- traverse (inlined caller) as
            w <- Data.Stateful.get
            case NameMap.lookup g w.small of
              Just d => if g /= caller && mayInline caller g && length as' == length d.params
                          then expanded fc d as'
                          else pure (Exp.FCall fc g as')
              Nothing => pure (Exp.FCall fc g as')
      Exp.FPrim fc n s l as => Exp.FPrim fc n s l <$> traverse (inlined caller) as
      Exp.FStatic _ _ _ _ => pure e
      Exp.FCon fc c t s l as => Exp.FCon fc c t s l <$> traverse (inlined caller) as
      Exp.FCase fc sc alts dflt =>
        [| Exp.FCase (pure fc) (inlined caller sc) (traverse alternative alts)
             (traverse (inlined caller) dflt) |]
      Exp.FCrash _ _ => pure e
      Exp.FNone _ => pure e
      where
        alternative : Exp.FlatAlt -> M Exp.FlatAlt
        alternative (Exp.FConAlt c t vs sc) = Exp.FConAlt c t vs <$> inlined caller sc
        alternative (Exp.FConstAlt c sc) = Exp.FConstAlt c <$> inlined caller sc

    ||| A call of the small form replaced by its body: each argument bound in
    ||| turn to a fresh copy of its parameter, then the body over the copies.
    expanded : FC -> Exp.FlatDef -> List Exp -> M Exp
    expanded fc d as = do
      names <- traverse (\p => fresh p.name) d.params
      let renamed = rename (SortedMap.fromList (zip (map (.name) d.params) names)) d.body
          params = zipWith (\p, n => { name := n } p) d.params names
      pure (foldr (\(p, a), sc => Exp.FLet fc p a sc) renamed (zip params as))
      where
        ||| The expression with each free variable the map names renamed: a binder
        ||| hides its own name from the map in its scope.
        rename : SortedMap Name Name -> Exp -> Exp
        rename m e = case e of
          Exp.FVar fc n => Exp.FVar fc (fromMaybe n (SortedMap.lookup n m))
          Exp.FLet fc v val sc =>
            Exp.FLet fc v (rename m val) (rename (SortedMap.delete v.name m) sc)
          Exp.FConst _ _ => e
          Exp.FOp fc op as => Exp.FOp fc op (map (rename m) as)
          Exp.FCall fc n as => Exp.FCall fc n (map (rename m) as)
          Exp.FPrim fc n s l as => Exp.FPrim fc n s l (map (rename m) as)
          Exp.FStatic _ _ _ _ => e
          Exp.FCon fc c t s l as => Exp.FCon fc c t s l (map (rename m) as)
          Exp.FCase fc sc alts dflt =>
            Exp.FCase fc (rename m sc) (map alternative alts) (map (rename m) dflt)
          Exp.FCrash _ _ => e
          Exp.FNone _ => e
          where
            alternative : Exp.FlatAlt -> Exp.FlatAlt
            alternative (Exp.FConAlt c t vs sc) =
              Exp.FConAlt c t vs (rename (foldl (flip SortedMap.delete) m (map (.name) vs)) sc)
            alternative (Exp.FConstAlt c sc) = Exp.FConstAlt c (rename m sc)

        ||| A fresh name for a parameter of an inlined body.
        fresh : Name -> M Name
        fresh x =
          Data.Stateful.state (\w => ({ nextName := w.nextName + 1 } w, MN (nameRoot x) w.nextName))

||| The forms with every call of a small form that `mayInline` lets its caller
||| take replaced by the form's body.
export
inlineSmall : (mayInline : (caller, callee : Name) -> Bool) -> NameMap Exp.FlatDef ->
              NameMap Exp.FlatDef
inlineSmall mayInline table =
  let (w, ()) = Data.Stateful.toPair
                  (Data.Stateful.outcome (MkWalk empty empty empty 0)
                     (traverse_ (walk table mayInline) (map fst (NameMap.toList table))))
  in w.done
