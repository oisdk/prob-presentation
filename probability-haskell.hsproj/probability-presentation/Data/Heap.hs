module Data.Heap where
  
import Data.Semigroup

data Heap a b
  = Nil
  | Heap a b (Heap a b) (Heap a b)

instance Ord a => Semigroup (Heap a b) where
  Nil <> ys = ys
  xs <> Nil = xs
  h1@(Heap i x lx rx) <> h2@(Heap j y ly ry)
    | i <= j    = Heap i x (h2 <> rx) lx
    | otherwise = Heap j y (h1 <> ry) ly
  stimes = stimesMonoid

instance Ord a => Monoid (Heap a b) where
  mappend = (<>)
  mempty = Nil
  
minView :: Ord a => Heap a b -> Maybe ((a,b), Heap a b)
minView Nil = Nothing
minView (Heap x y l r) = Just ((x,y), mappend l r)

singleton :: a -> b -> Heap a b
singleton x y = Heap x y Nil Nil

insertHeap :: Ord a => a -> b -> Heap a b -> Heap a b
insertHeap x y = mappend (singleton x y)

instance Ord a => Foldable (Heap a) where
    foldr f b Nil = b
    foldr f b (Heap _ x l r) = f x (foldr f b (mappend l r))