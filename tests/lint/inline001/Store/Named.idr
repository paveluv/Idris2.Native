||| A shorthand, `Named v` for `Tag String v`, which `inline-alias` replaces
||| by what it names, here as in `Plan`, and takes out.
module Store.Named

import Store.Tag

%default total

||| A value tagged with a name.
public export
Named : Type -> Type
Named v = Tag String v

||| A value named after itself.
export
named : Show v => v -> Named v
named x = MkTag (show x) x
