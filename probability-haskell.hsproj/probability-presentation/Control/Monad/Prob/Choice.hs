{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Prob.Choice where
    
import Control.Monad.Free
import Data.Heap
import Control.Monad.Prob.Class

data Choice a = Choose Rational a a deriving (Functor,Show)

type Dist = Free Choice

instance Expect Dist where
    expect p = iter f . fmap p where
      f (Choose nd x y) = nd * x + (1-nd) * y

instance Distribution Dist where
    distrib p = go . foldMap (\x -> let (y,yp) = p x in singleton yp (Pure y))
      where
        go xs = case minView xs of
          Nothing -> error "empty list"
          Just ((xp,x),ys) -> case minView ys of
            Nothing -> x
            Just ((yp,y),zs) ->
              go (insertHeap (xp+yp) (Free (Choose (xp/(xp+yp)) x y)) zs)