-- A character as a string, natively: the cast conses the character onto
-- the empty string, a static object that the compiler makes whether or not
-- the program writes "" itself, as this one does not. Characters of one to
-- four bytes in UTF-8.
module Main

%noinline
chars : List Char
chars = [chr 65, chr 955, chr 8364, chr 128512]

main : IO ()
main = traverse_ (\c => putStrLn (cast c)) chars
