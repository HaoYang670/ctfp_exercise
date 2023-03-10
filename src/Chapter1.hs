module Chapter1(test_composition_identity) where

-- | Implement, as best as you can, the identity function in your favorite language
identity :: a -> a
identity a = a

-- | Implement the composition function in your favorite language.
composition :: (b -> c) -> (a -> b) -> a -> c
composition g f x = g (f x)

-- | Write a program that tries to test that your composition function respects identity.
test_composition_identity :: (Eq b) => (a -> b) -> a -> Bool
test_composition_identity f v =
  f v == composition f identity v && f v == composition identity f v

-- When is a directed graph a category?
-- I don't know. Allow >=2 edges between 2 nodes?