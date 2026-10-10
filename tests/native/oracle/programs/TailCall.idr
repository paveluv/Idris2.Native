-- Self and mutual tail calls, many of them: under the native backend each is
-- a jump, so neither the stack nor the heap grows with the count.
module Main

loop : Int -> Int -> Int
loop 0 acc = acc
loop n acc = loop (n - 1) (acc + 2)

mutual
  isEven : Int -> Bool
  isEven 0 = True
  isEven n = isOdd (n - 1)

  isOdd : Int -> Bool
  isOdd 0 = False
  isOdd n = isEven (n - 1)

main : IO ()
main = do
  printLn (loop 100000 0)
  printLn (isEven 100001, isOdd 100001)
