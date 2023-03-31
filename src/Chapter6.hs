module Chapter6 where

-- | Show the isomorphism between Maybe a and Either () a.
f :: Maybe a -> Either () a
f Nothing = Left ()
f (Just x) = Right x

fInverse :: Either () a -> Maybe a
fInverse (Left ()) = Nothing
fInverse (Right x) = Just x

-- | Show that 𝑎 + 𝑎 = 2 × 𝑎 holds for types (up to isomorphism)
data LeftType  a = This a | That a
type RightType a = (Bool, a)

lToR :: LeftType a -> RightType a
lToR (This x) = (True, x)
lToR (That x) = (False, x)

rToL :: RightType a -> LeftType a
rToL (True, x) = This x
rToL (False, x) = That x
