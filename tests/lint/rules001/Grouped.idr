||| A name qualified as it should be: its module imported as its group,
||| `One`, and the name written `One.item`. No finding.
module Grouped

import Shared.One.Item as One

%default total

||| The item.
export
the1 : Nat
the1 = One.item
