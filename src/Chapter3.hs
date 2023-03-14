{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Monoid law, left identity" #-}
{-# HLINT ignore "Monoid law, right identity" #-}
module Chapter3(testAddMod3Identity, testAddMod3Assoc) where

-- | Considering that Bool is a set of two values True and False,
-- show that it forms two (set-theoretical) monoids with respect to,
-- respectively, operator && (AND) and || (OR).

newtype AndBool = AndBool Bool
newtype OrBool = OrBool Bool

instance Semigroup AndBool where
  (<>) (AndBool a) (AndBool b) = AndBool (a && b)

instance Semigroup OrBool where
  (<>) (OrBool a) (OrBool b) = OrBool (a || b)

instance Monoid AndBool where
  mempty = AndBool True

instance Monoid OrBool where
  mempty = OrBool False

-- | Represent addition modulo 3 as a monoid category.

data ZOT = Zero | One | Two deriving (Eq)

addMod3 :: ZOT -> ZOT -> ZOT
addMod3 a b = case (a, b) of
  (Zero, n) -> n
  (n, Zero) -> n
  (One, One) -> Two
  (One, Two) -> Zero
  (Two, One) -> Zero
  (Two, Two) -> Zero

instance Semigroup ZOT where
  (<>) = addMod3

instance Monoid ZOT where
  mempty = Zero

testAddMod3Identity :: IO Bool
testAddMod3Identity = do
  putStrLn "test Addition modulo 3 identity"
  let result = all (\n -> n <> mempty == n && mempty <> n == n) [Zero, One, Two]
  return result

testAddMod3Assoc :: IO Bool
testAddMod3Assoc = do
  putStrLn "test Addition modulo 3 associtivity"
  let result = (One <> One <> Two) == (One <> (One <> Two))
  return result
