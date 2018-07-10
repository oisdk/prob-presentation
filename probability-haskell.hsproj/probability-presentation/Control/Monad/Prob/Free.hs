{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wincomplete-record-updates #-}
{-# OPTIONS_GHC -Wmonomorphism-restriction #-}
{-# OPTIONS_GHC -Wmissing-exported-signatures #-}
{-# OPTIONS_GHC -Widentities #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}

module Control.Monad.Prob.Free where

import           Control.Monad.Free
import           Control.Monad.Prob.Class
import           Data.Heap

-- | The base functor for a probabilistic language.
-- The @choose@ combinator from:
--
-- [N. Ramsey and A. Pfeffer, ‘Stochastic Lambda Calculus and Monads of
-- Probability Distributions’, in 29th ACM SIGPLAN-SIGACT symposium on
-- Principles of programming languages, 2002, vol. 37, pp.
-- 154–165.](http://www.cs.tufts.edu/~nr/cs257/archive/norman-ramsey/pmonad.pdf)
data Choice a =
    Choose Rational a a
    deriving (Functor,Foldable,Traversable,Show)

-- | The probability monad.
newtype Dist a
  = Dist
  { runDist :: Free Choice a
  } deriving (Functor,Foldable,Traversable,Applicative,Monad,Show)

instance Expect Dist where
    expect p = iter f . runDist . fmap p
      where
        f (Choose nd x y) = nd * x + (1 - nd) * y

instance Distribution Dist where
    -- | Uses Huffman's algorithm.
    distrib p =
        Dist . go . foldMap (\x -> let (y,yp) = p x in singleton yp (Pure y))
      where
        go xs =
            case minView xs of
                Nothing -> error "empty list"
                Just ((xp,x),ys) ->
                    case minView ys of
                        Nothing -> x
                        Just ((yp,y),zs) ->
                            go
                                (insertHeap
                                     (xp + yp)
                                     (Free (Choose (xp / (xp + yp)) x y))
                                     zs)
