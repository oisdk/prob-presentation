{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wincomplete-record-updates #-}
{-# OPTIONS_GHC -Wmonomorphism-restriction #-}
{-# OPTIONS_GHC -Wmissing-exported-signatures #-}
{-# OPTIONS_GHC -Widentities #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}

module Control.Monad.Prob.Cofree where
    
import Control.Comonad.Cofree
import Control.Comonad
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Monad.Prob.Class
import Data.Foldable
import Control.Monad

data Perhaps a
    = Impossible
    | WithChance Rational a
    deriving (Functor,Foldable,Traversable,Show)

newtype Dist a
    = Dist
    { runDist :: Cofree Perhaps a
    } deriving (Functor,Foldable)
    
instance Comonad Dist where
    extract (Dist xs) = extract xs
    duplicate (Dist xs) = Dist (fmap Dist (duplicate xs))

foldDist :: (a -> Rational -> b -> b) -> (a -> b) -> Dist a -> b
foldDist f b = r . runDist
  where
    r (x :< Impossible) = b x
    r (x :< WithChance p xs) = f x p (r xs)

instance Distribution Dist where
    distrib p inp = Dist $ f (tot*lst) nelist
      where
        nelist = (NonEmpty.fromList . map p . toList) inp
        (tot,lst) = foldl' (\(!t,_) e -> (t+e,e)) (0,undefined) (fmap snd nelist)
        f _ ((x,_) :| []) = x :< Impossible
        f n ((x,xp) :| (x' : xs)) = x :< WithChance (mp / np) (f np (x' :| xs))
          where
            mp = xp * lst
            np = n - mp

instance Expect Dist where
    expect p = foldDist f p
      where
        f x n xs = (p x * n + xs) / (n + 1)

instance Applicative Dist where
    pure x = Dist (x :< Impossible)
    (<*>) = ap
    
choose :: Rational -> Dist a -> Dist a -> Dist a
choose = flip (foldDist f (\x y ->  Dist . (x :<) . WithChance y . runDist))
  where
    f e r a p = Dist . (e :<) . WithChance ip . runDist . a op
      where
        ip = p * r / (p + r + 1)
        op = p / (r + 1)

instance Monad Dist where
    xs >>= f = foldDist (flip choose . f) f xs
