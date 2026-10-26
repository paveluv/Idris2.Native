-- Constants Idris inlines. `alias` is `public export`, with a body as
-- simple as a name, so as Idris builds the module it puts the body in
-- place of each use, as if `main` were written
--
--   main = printLn (uncheckedWord squares 3 0, 5)
--
-- and no use is left to read `alias`. The mark is refused, with the fix:
-- `export`, whose body no other module sees, or `%noinline`. `five` is
-- inlined because its `%inline` asks for it, and it is not `public
-- export`, so the fix is to remove that, which `%noinline` could not join.
module Inlined

import Native.Types.Bytes

%cg native static Inlined.alias Inlined.five

squares : Bytes
squares = generate 4 (\i => cast (i * i))

public export
alias : Bytes
alias = squares

%inline
export
five : Int
five = 5

main : IO ()
main = printLn (uncheckedWord alias 3 0, five)
