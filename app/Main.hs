{-# LANGUAGE BlockArguments #-}
module Main where

import Chapter1 (test_composition_identity)
import Chapter2(testMemoize)
import Chapter3(testAddMod3Identity, testAddMod3Assoc)

main :: IO ()
main = do
  doTestCompositionIdentity
  doTestMemoize
  doTestAddMod3


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

doTestAddMod3 :: IO ()
doTestAddMod3 = do
  result <- testAddMod3Identity
  putStrLn (if result then "PASS" else "FAIL")
  result <- testAddMod3Assoc
  putStrLn (if result then "PASS" else "FAIL")
