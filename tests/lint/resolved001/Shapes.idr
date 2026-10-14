||| A façade: it defines nothing and re-exports `Shape`, for importers
||| outside the code linted, as a program imports the runtime's. A module of
||| ours that reaches `Shape` only through it is reported all the same.
module Shapes

import public Shape

%default total
