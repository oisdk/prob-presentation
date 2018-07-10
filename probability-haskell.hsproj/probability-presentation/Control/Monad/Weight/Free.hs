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

module Control.Monad.Weight.Free where
    
import Control.Monad.Trans.Free
import Control.Monad.Prob.Class
import Data.Foldable

newtype Dist a
    = Dist
    { runDist :: FreeT ((,) Rational) [] a
    } deriving (Functor,Foldable,Traversable,Applicative,Monad,Show)

instance Distribution Dist where
    distrib p = Dist . FreeT . map f . toList
      where
        f x = case p x of
            (y, yp) -> Free (yp, pure y)
            
instance Expect Dist where
    expect p (Dist (FreeT xs')) = sum (map f xs') / sum (map g xs')
      where
        f (Pure x) = p x
        f (Free (xp, xs)) = expect p (Dist xs) * xp
        g (Pure _) = 1
        g (Free (xp, _)) = xp

coin :: Dist Bool
coin = uniform [False,True]

pairacoin :: Dist (Bool,Bool)
pairacoin = do
    x <- coin
    y <- coin
    return (x,y)
    

die :: Dist Int
die = uniform [1..6]

pairadice :: Dist (Int,Int)
pairadice = do
    x <- die
    y <- die
    return (x,y)
--
--math :: Doc -> Doc
--math d = char '$' <> d <> char '$'
--
--docRational :: Rational -> Doc
--docRational r | denominator r == 1 = math $ integer (numerator r)
--docRational r = math $ text "\\frac" <> braces (integer (numerator r)) <> braces (integer (denominator r))
--
--showTree :: (a -> Doc) -> Dist a -> Doc
--showTree s tr@(FreeT xs) = showTree' (g xs) tr
--  where
--    showTree' p (FreeT xs) = brackets (hang (docRational p) 2 (vcat (map f xs)))
--      where
--        f (Pure x) = brackets (braces (s x))
--        f (Free (x, xs)) = showTree' x xs
--    g = sum . map (\case
--        Pure _ -> 1
--        Free (x,_) -> x) 
--        
--data Decision = Decision
--  { switch :: Bool
--  , stick  :: Bool }
--   
--montyHall :: Dist Decision
--montyHall = do
--    car <- uniform [1..3]
--    firstChoice <- uniform [1..3]
--    let revealed  = head [ door | door <- [1..3], door /= firstChoice, door /= car ]
--    let newChoice = head [ door | door <- [1..3], door /= firstChoice, door /= revealed ]
--    return (Decision { switch = newChoice == car
--                     , stick  = firstChoice == car })
--     
--docDecision (Decision sw st) = char (bool '0' '1' st) <> char (bool '0' '1' sw)
--
--
--
--
--
--
--
