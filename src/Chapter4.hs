module Chapter4(testSafeRootReciprocal) where
import GHC.Float (sqrtFloat)
import Data.Maybe (isNothing)

class Kleisli k where
  (>=>) :: (a -> k b) -> (b -> k c) -> a -> k c

-- | Construct the Kleisli category for partial functions
instance Kleisli Maybe where
  (>=>) f g a = g =<< f a

safeReciprocal :: Float -> Maybe Float
safeReciprocal 0 = Nothing
safeReciprocal n = Just (1 / n)

safeRoot :: Float -> Maybe Float
safeRoot n
  | n >= 0 = Just (sqrtFloat n)
  | n < 0 = Nothing

-- | Compose the functions safeRoot and safeReciprocal to implement safeRootReciprocal
-- that calculates sqrt(1/x) whenever possible.
safeRootReciprocal :: Float -> Maybe Float
safeRootReciprocal = safeReciprocal >=> safeRoot

testSafeRootReciprocal :: IO Bool
testSafeRootReciprocal = do
  putStrLn "Test testSafeRootReciprocal"
  let rs1 = safeRootReciprocal 4 == Just (1 / 2)
  let rs2 = isNothing (safeRootReciprocal 0)
  return (rs1 && rs2)
