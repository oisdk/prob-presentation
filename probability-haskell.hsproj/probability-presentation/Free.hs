{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wall #-}

module Free where
    
{-# LANGUAGE FlexibleInstances, BangPatterns #-}

{-# options_ghc -Wall #-}

import Data.Functor.Compose
import Linear.V2
import Data.Monoid (Product(..))
import Control.Monad.Free
import Data.Bool
import GHC.Real
import Data.Heap
import Control.Applicative
import Control.Monad

data Choose a = Choose Rational a a | Impossible deriving Functor


instance Applicative Choose where
instance Alternative Choose where
    empty = Impossible
    

type Dist = Free Choose

expect :: (a -> Rational) -> Dist a -> Rational
expect p = iter f . fmap p where
  f (Choose nd x y) = (x+y) / nd
  f Impossible = 0

fromList :: (a -> Rational) -> [a] -> Dist a
fromList p = go . foldMap (\x -> singleton (p x) (Pure x))
  where
    go xs = case minView xs of
      Nothing -> error "empty list"
      Just ((xp,x),ys) -> case minView ys of
        Nothing -> x
        Just ((yp,y),zs) -> go (insertHeap (xp+yp) (Free (Choose (xp + yp) x y)) zs)

uniform :: [a] -> Dist a
uniform = fromList (const 1)


data Gender = Boy | Girl deriving (Show,Eq,Ord)

data Child
  = Child
  { gender :: Gender
  , age    :: Int
  }
  
child :: Dist Child
child = do
    gn <- uniform [Boy,Girl]
    ag <- uniform [1..17]
    return (Child gn ag)
    
mrJones :: Dist [Child]
mrJones = do
  child1 <- child
  child2 <- child
  if age child1 > age child2
    then guard (gender child1 == Girl)
    else guard (gender child2 == Girl)
  return [child1, child2]

mrSmith :: Dist [Child]
mrSmith = do
  child1 <- child
  child2 <- child
  guard (gender child1 == Boy || gender child2 == Boy)
  return [child1, child2]


probOf :: (a -> Bool) -> Dist a -> Rational
probOf p = expect (\x -> if p x then 1 else 0)