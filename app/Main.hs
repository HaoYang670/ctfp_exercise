{-# LANGUAGE BlockArguments #-}
module Main where

import Chapter1 (test_composition_identity)
import Chapter2(testMemoize)

main :: IO ()
main = do
  doTestCompositionIdentity
  doTestMemoize


doTestCompositionIdentity :: IO ()
doTestCompositionIdentity = do
  putStrLn "test composition function respects identity:"
  print (test_composition_identity (+ 3) 10)

doTestMemoize :: IO ()
doTestMemoize = do
  result <- testMemoize fib 31
  putStrLn
    if result 
    then
      "memoized function gets same result."
    else
      "memoized function gets diff result."
  return ()
  where
    fib :: Int -> Integer
    fib 0 = 0
    fib 1 = 1
    fib n = fib(n-1) + fib(n-2)
