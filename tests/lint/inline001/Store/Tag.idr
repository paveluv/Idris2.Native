||| A value with a tag.
module Store.Tag

%default total

||| A value `v` tagged with a `t`.
public export
data Tag : Type -> Type -> Type where
  MkTag : t -> v -> Tag t v
