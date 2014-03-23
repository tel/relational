{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE TypeOperators     #-}

-- |
-- Module      :  Rel.Internal.Types
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Some utility types.
--
module Rel.Internal.Types (

    (:::) (..)
  , Only (..)
                 
) where

import           Control.Applicative
import           Data.Foldable       (Foldable)
import           Data.Traversable    (Traversable)
import           GHC.TypeLits

-- | @(nm ::: t)@ is a named attribute type of 
-- type @t@ and name @nm@.
data (:::) :: Symbol -> * -> * where
  Attribute :: sy ::: t

-- | Isomorphic to 'Data.Functor.Identity'; essentially this 
-- is a 1-tuple. Useful for building 'Rel'ations of degree 1.
newtype Only a = Only { getOnly :: a }
  deriving ( Eq, Ord, Show, Read
           , Functor, Foldable, Traversable
           )

instance Applicative Only where
  pure = Only
  Only f <*> Only x = Only (f x)

instance Monad Only where
  return = pure
  Only x >>= f = f x
