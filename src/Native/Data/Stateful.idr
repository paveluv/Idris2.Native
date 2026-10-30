||| Steps over a state, each giving a result or failing (`Stateful`): what
||| a state monad over `Either` does, with no monad under it, so that a
||| bind is one call of its own, which matches the step's outcome once, and
||| calls no other monad's methods through their dictionaries. One that
||| cannot fail fails with `Void`.
module Native.Data.Stateful

%default total

||| Where a computation over a state ends: the state it leaves and its
||| result, or its failure. Abstract: read by `toEither` and `toPair`.
export
data Outcome : (s, e, a : Type) -> Type where
  Ok : s -> a -> Outcome s e a
  Failed : e -> Outcome s e a

||| A computation over the state `s` that gives an `a` or fails with an
||| `e`. Abstract: made by its interfaces' methods and by `get`, `put`,
||| `modify`, `state` and `failWith`.
export
record Stateful (s, e, a : Type) where
  constructor MkStateful
  step : s -> Outcome s e a

export
Functor (Stateful s e) where
  map f m = MkStateful $ \st => case m.step st of
    Ok st' x => Ok st' (f x)
    Failed err => Failed err

export
Applicative (Stateful s e) where
  pure x = MkStateful $ \st => Ok st x
  mf <*> mx = MkStateful $ \st => case mf.step st of
    Ok st' f => case mx.step st' of
      Ok st'' x => Ok st'' (f x)
      Failed err => Failed err
    Failed err => Failed err

export
Monad (Stateful s e) where
  m >>= k = MkStateful $ \st => case m.step st of
    Ok st' x => (k x).step st'
    Failed err => Failed err

||| The state.
export %inline
get : Stateful s e s
get = MkStateful $ \st => Ok st st

||| The state replaced.
export %inline
put : s -> Stateful s e ()
put st = MkStateful $ \_ => Ok st ()

||| The state changed by the function.
export %inline
modify : (s -> s) -> Stateful s e ()
modify f = MkStateful $ \st => Ok (f st) ()

||| The state changed, and a result given, by the function, in one step.
export %inline
state : (s -> (s, a)) -> Stateful s e a
state f = MkStateful $ \st => let (st', x) = f st in Ok st' x

||| A failure, whatever the result's type.
export %inline
failWith : e -> Stateful s e a
failWith err = MkStateful $ \_ => Failed err

||| Where the computation ends from the state.
export
outcome : s -> Stateful s e a -> Outcome s e a
outcome st m = m.step st

||| An outcome as an `Either`: the failure, or the state and the result.
export
toEither : Outcome s e a -> Either e (s, a)
toEither (Ok st x) = Right (st, x)
toEither (Failed err) = Left err

||| The outcome of a computation that cannot fail: its state and its
||| result.
export
toPair : Outcome s Void a -> (s, a)
toPair (Ok st x) = (st, x)
toPair (Failed err) = absurd err
