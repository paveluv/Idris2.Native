||| A module that lists the context's names by Idris's `allNames`, which
||| looks up every entry, and so decodes every definition of the context,
||| to give their names: reported (`decoding-walk`), where it is written.
||| The names of the context's map from full names to entries,
||| `resolvedAs`, which decodes none, are not.
module Walk

import Core.Context
import Core.Context.Context
import Core.Core
import Core.Name
import Libraries.Data.NameMap

%default covering

export
everyName : Context -> Core (List Name)
everyName ctxt = allNames ctxt

export
byTable : Context -> List Name
byTable ctxt = keys (resolvedAs ctxt)
