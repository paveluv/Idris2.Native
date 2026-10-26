-- Makers refused: a program that imports the module `Native.Types.Fake`,
-- whose two makers are not as the code generator takes makers, is not
-- compiled, whatever it marks, and the error says what is wrong with
-- each.
module Maker

import Native.Types.Fake

main : IO ()
main = putStrLn "not reached"
