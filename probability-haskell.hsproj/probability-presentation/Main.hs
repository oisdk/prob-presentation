{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

import Control.Monad
import Data.Ratio
import Control.Applicative
import Control.Monad.Prob.Class
--import Control.Monad.Prob.List
    
--data Gender = Boy | Girl deriving (Show,Eq,Ord)
--
--data Child
--  = Child
--  { gender :: Gender
--  , age    :: Int
--  }
--  
--child :: (Distribution m, Monad m) => m Child
--child = do
--    gn <- uniform [Boy,Girl]
--    ag <- uniform [1..17]
--    return (Child gn ag)
--    
--mrJones :: (Alternative m, Distribution m, Monad m) => m [Child]
--mrJones = do
--  child1 <- child
--  child2 <- child
--  if age child1 > age child2
--    then guard (gender child1 == Girl)
--    else guard (gender child2 == Girl)
--  return [child1, child2]
--
--mrSmith :: (Alternative m, Distribution m, Monad m) => m [Child]
--mrSmith = do
--  child1 <- child
--  child2 <- child
--  guard (gender child1 == Boy || gender child2 == Boy)
--  return [child1, child2]
--
--prob1 :: forall m. (Alternative m, Distribution m, Monad m, Expect m) => Rational
--prob1 = probOf (all ((==) Girl . gender)) (mrJones @ m)
--
--prob2 :: forall m. (Alternative m, Distribution m, Monad m, Expect m) => Rational
--prob2 = probOf (all ((==) Boy  . gender)) (mrSmith @ m)