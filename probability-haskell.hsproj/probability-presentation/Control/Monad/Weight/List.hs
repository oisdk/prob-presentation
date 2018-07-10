{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Monad.Weight.List where
    
import Control.Monad.Prob.Class
import Control.Lens
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad
import Control.Applicative
import Data.Function

newtype Dist a
    = Dist
    { runDist :: [(a, Rational)]
    } deriving (Functor, Foldable, Traversable)

_Compressed :: Ord a => Iso (Dist a) (Dist b) (Map a Rational) (Map b Rational)
_Compressed = iso (Map.fromListWith (+) . runDist) (Dist .  Map.toList)

instance (Ord a, Show a) => Show (Dist a) where
    showsPrec n = views _Compressed (showsPrec n)
    
instance (Ord a) => Eq (Dist a) where
    (==) = (==) `on` view _Compressed

instance Applicative Dist where
    pure x = Dist [(x, 1)]
    (<*>) = ap

instance Monad Dist where
    xs >>= f = Dist [ (y, xp*yp)
                    | (x,xp) <- runDist xs
                    , (y,yp) <- runDist (f x) ]
                    
instance Alternative Dist where
    empty = Dist []
    Dist xs <|> Dist ys = Dist (xs ++ ys)
    
instance Distribution Dist where
    distrib f = Dist . foldr (\x xs -> f x : xs) []
    
instance Expect Dist where
    expect p xs
      = sum [ p x * xp | (x,xp) <- runDist xs ] / sum (map snd (runDist xs))
