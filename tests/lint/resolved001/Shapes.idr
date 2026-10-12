||| A façade: it defines nothing and re-exports `Shape`. Re-exporting is
||| what a façade is for, so a module that reaches `Shape` through it
||| reaches it as meant.
module Shapes

import public Shape

%default total
