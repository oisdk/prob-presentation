{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Control.Monad.Prob.Weight where
    
import Control.Monad.Trans.Free
import Linear.V2
import Data.Ratio
import Data.Monoid
import Control.Monad.Prob.Class
import Data.Heap
import qualified Data.Tree.Binary.Internal as Tree
import Text.PrettyPrint hiding ((<>))
import Data.List
import Data.Bool
import Control.Monad

type Dist = FreeT ((,) Rational) []

instance Distribution Dist where
    distrib p xs = FreeT (foldr f [] xs)
      where
        f x xs = case p x of
            (y, yp) -> Free (yp, pure y) : xs
            
instance Expect Dist where
    expect p (FreeT xs) = sum (map f xs) / sum (map g xs)
      where
        f (Pure x) = p x
        f (Free (xp, xs)) = expect p xs * xp
        g (Pure x) = 1
        g (Free (xp, xs)) = xp

coin :: Dist Bool
coin = uniform [False,True]

--pairadice :: Rational
pairacoin = do
    x <- coin
    y <- coin
    return (x,y)
    

die :: Dist Int
die = uniform [1..6]

pairadice = do
    x <- die
    y <- die
    return (x,y)

math :: Doc -> Doc
math d = char '$' <> d <> char '$'

docRational :: Rational -> Doc
docRational r | denominator r == 1 = math $ integer (numerator r)
docRational r = math $ text "\\frac" <> braces (integer (numerator r)) <> braces (integer (denominator r))

showTree :: (a -> Doc) -> Dist a -> Doc
showTree s tr@(FreeT xs) = showTree' (g xs) tr
  where
    showTree' p (FreeT xs) = brackets (hang (docRational p) 2 (vcat (map f xs)))
      where
        f (Pure x) = brackets (braces (s x))
        f (Free (x, xs)) = showTree' x xs
    g = sum . map (\case
        Pure _ -> 1
        Free (x,_) -> x) 
        
data Decision = Decision
  { switch :: Bool
  , stick  :: Bool }
   
montyHall :: Dist Decision
montyHall = do
    car <- uniform [1..3]
    firstChoice <- uniform [1..3]
    let revealed  = head [ door | door <- [1..3], door /= firstChoice, door /= car ]
    let newChoice = head [ door | door <- [1..3], door /= firstChoice, door /= revealed ]
    return (Decision { switch = newChoice == car
                     , stick  = firstChoice == car })
     
docDecision (Decision sw st) = char (bool '0' '1' st) <> char (bool '0' '1' sw)







