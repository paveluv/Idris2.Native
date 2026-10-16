||| A module that makes a raw address from a word, which only the modules
||| that keep addresses as words may: reported (`raw-maker`). A count taken
||| for an address is the mistake the rule keeps out.
module Page

import Native.Runtime.Raw

%default total

export
page : Raw
page = fromWord 4096
