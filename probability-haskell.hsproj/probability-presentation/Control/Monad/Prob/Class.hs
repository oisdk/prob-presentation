{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Control.Monad.Prob.Class (Distribution(..), Expect(..)) where
    
import Data.Ratio
import Data.Foldable
import Data.Bool

newtype Fold a
    = Fold
    { runFold :: forall b. (a -> b -> b) -> b -> b }
    
instance Foldable Fold where
    foldr f b (Fold xs) = xs f b
    {-# INLINE foldr #-}

class Distribution m where
    {-# MINIMAL distrib #-}
    distrib :: Foldable f => (a -> (b, Rational)) -> f a -> m b
    
    uniform :: [a] -> m a
    uniform xs = distrib id ys
      where
        (n,ys) = foldl' (\( !ln, acc) e -> (ln + 1, cons e m acc)) (0,nil) xs
        nil = Fold (\_ b -> b)
        cons e m xs = Fold (\f b -> f (e,m) (runFold xs f b))
        m = 1 % toEnum n

class Expect m where
    {-# MINIMAL expect #-}
    expect :: (a -> Rational) -> m a -> Rational
    probOf :: (a -> Bool) -> m a -> Rational
    probOf p = expect (bool 0 1 . p)
    

