{-# LANGUAGE BlockArguments #-}
module Main where

import Chapter1 (test_composition_identity)
import Chapter2(testMemoize)
import Chapter3(testAddMod3Identity, testAddMod3Assoc)
import Chapter4(testSafeRootReciprocal)

main :: IO ()
main = do
  doTestCompositionIdentity
  doTestMemoize
  doTestAddMod3
  doTestSafeRootReciprocal


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
  putStrLn (if result then "  PASS" else "  FAIL")
  result <- testAddMod3Assoc
  putStrLn (if result then "  PASS" else "  FAIL")

doTestSafeRootReciprocal :: IO ()
doTestSafeRootReciprocal = do
  result <- testSafeRootReciprocal
  putStrLn (if result then "  Pass" else "  FAIL")
