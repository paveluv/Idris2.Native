||| `Plain` writes names of our modules bare: `frame`, of `Frame`, and
||| `Square`, of `Shape`, each written with its module's name by the rule:
||| `unqualified`. `Shape`, the type its module is named after, is written
||| bare, and `Frame.frame` as the rule writes it.
module Plain

import Frame
import Shape

%default total

export
plain : Shape -> Shape
plain s = frame (Frame.frame s)

export
unit : Shape
unit = Square 1
