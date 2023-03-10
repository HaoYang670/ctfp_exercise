module Main where

import Chapter1 (test_composition_identity)

main :: IO ()
main = do
  doTestCompositionIdentity

doTestCompositionIdentity :: IO ()
doTestCompositionIdentity = do
  putStrLn "test composition function respects identity:"
  print (test_composition_identity (+ 3) 10)
