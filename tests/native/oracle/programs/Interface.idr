-- Interfaces: a user interface with a default method, instances for a base
-- type and for a list of any instance, passed as dictionaries.
module Main

interface Describe a where
  describe : a -> String
  shout : a -> String
  shout x = describe x ++ "!"

Describe Bool where
  describe b = if b then "yes" else "no"

Describe Int where
  describe n = "int " ++ show n

Describe a => Describe (List a) where
  describe xs = "[" ++ concatMap (\x => describe x ++ ";") xs ++ "]"

main : IO ()
main = do
  putStrLn (describe True)
  putStrLn (shout (the Int 5))
  putStrLn (describe (the (List Int) [1, 2, 3]))
  putStrLn (describe [[True], [False, True]])
