{-# LANGUAGE DeriveFunctor #-}

import Control.Monad
import Data.Ratio
import Control.Applicative


newtype Dist a = Dist { runDist :: [(a, Rational)] } deriving (Show, Functor)

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
    

uniform :: [a] -> Dist a
uniform xs = Dist [ (x,p) | x <- xs ]
  where
    p = 1 % toEnum (length xs)
    
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

expect :: (a -> Rational) -> Dist a -> Rational
expect p xs
  = sum [ p x * xp | (x,xp) <- runDist xs ] / sum (map snd (runDist xs))


probOf :: (a -> Bool) -> Dist a -> Rational
probOf p = expect (\x -> if p x then 1 else 0)


