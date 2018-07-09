{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}

module Control.Monad.Prob.List where
    
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
    } deriving (Functor, Foldable)

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

--data Gender = Boy | Girl deriving (Show,Eq,Ord)
--
--data Child
--  = Child
--  { gender :: Gender
--  , age    :: Int
--  }
--  
--child :: Dist Child
--child = do
--    gn <- uniform [Boy,Girl]
--    ag <- uniform [1..17]
--    return (Child gn ag)
--    
--mrJones :: Dist [Child]
--mrJones = do
--  child1 <- child
--  child2 <- child
--  if age child1 > age child2
--    then guard (gender child1 == Girl)
--    else guard (gender child2 == Girl)
--  return [child1, child2]
--
--mrSmith :: Dist [Child]
--mrSmith = do
--  child1 <- child
--  child2 <- child
--  guard (gender child1 == Boy || gender child2 == Boy)
--  return [child1, child2]
--

--
--
--probOf :: (a -> Bool) -> Dist a -> Rational
--probOf p = expect (\x -> if p x then 1 else 0)
--
--
