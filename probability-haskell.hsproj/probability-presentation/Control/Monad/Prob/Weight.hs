{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Prob.Weight where
    
import Control.Monad.Trans.Free
import Linear.V2
import Data.Ratio
import Data.Monoid
import Control.Monad.Prob.Class
import Data.Heap
import qualified Data.Tree.Binary.Internal as Tree
import Text.PrettyPrint hiding ((<>))

type Dist = FreeT [] ((,) (Product Rational))

instance Distribution Dist where
    distrib p xs = FreeT (Product 1, Free (foldr f [] xs))
      where
        f x xs = case p x of
            (y, yp) -> FreeT (Product yp, Pure y) : xs
            
instance Expect Dist where
    expect p xs = getProduct (fst (iterT f (xs >>= (\x -> FreeT (Product (p x), Pure ())))))
      where
        f xs = ((Product . sum . map (getProduct . fst)) xs, ())

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

showTree :: Show a => Dist a -> Doc
showTree (FreeT (Product p, Pure x)) = brackets (docRational p <+> brackets (braces $ text (show x)))
showTree (FreeT (Product p, Free xs)) = brackets (hang (docRational p) 2 (vcat (map showTree xs)))