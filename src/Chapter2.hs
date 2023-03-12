module Chapter2(testMemoize) where
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

-- | Define a function `memoize` which takes a pure function `f`
-- and returns a function that behaves almost exactly like `f`,
-- except that it only calls the original function once for every argument, stores the result internally,
-- and subsequently returns this stored result every time it’s called with the same argument.
-- We corrently only implement the (Int -> b) type, other types can be more complicate.
-- Find more from : https://wiki.haskell.org/Memoization
memoize :: (Int -> b) -> (Int -> b)
memoize f = (map f [0..] !!)

testMemoize :: (Eq b, Show b) => (Int-> b) -> Int -> IO Bool
testMemoize f n = do
  let memoizeF = memoize f
  start <- getCPUTime
  let result1 = memoizeF n
  putStrLn ("First time result: " ++ show result1)
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10^12)
  printf "First computation time: %0.9f sec\n" (diff :: Double)

  start <- getCPUTime
  let result2 = memoizeF n
  putStrLn ("Second time result: " ++ show result2)
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10^12)
  printf "Second computation time: %0.9f sec\n" (diff :: Double)
  return (result1 == result2)

