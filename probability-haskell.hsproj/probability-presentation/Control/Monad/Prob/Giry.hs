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

module Control.Monad.Prob.Giry where
    
import Control.Monad.Cont
import Control.Monad.Prob.Class

newtype Giry a
    = Giry
    { runGiry :: Cont Rational a
    } deriving (Functor,Applicative,Monad)
    
instance Expect Giry where
    expect = flip (runCont . runGiry)