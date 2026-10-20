||| A module that makes a byte address from a word, which only the modules
||| that keep addresses as words may: reported (`byte-addr-maker`). A count
||| taken for an address is the mistake the rule keeps out.
module Page

import Native.Runtime.ByteAddr

%default total

export
page : ByteAddr
page = fromWord 4096
