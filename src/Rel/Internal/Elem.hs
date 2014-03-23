{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TypeOperators     #-}

-- |
-- Module      :  Rel.Internal.Elem
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Proof witnesses exemplifying that a particular value is an
-- element of a type-level list. If you have a value of type @Elem
-- x xs@ then @xs@ must be of kind @[k]@, @x@ of kind @x@, and @x@
-- is an element of @xs@.
--
module Rel.Internal.Elem ( 

    Elem (..)
  , IElem
                
) where

import           Rel.Internal.Implicit

-- | Constructive proof object demonstrating that an element is
-- contained in a type-level list.
data Elem :: k -> [k] -> * where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

-- | Implicit construction of an 'Elem' proof.
type IElem x xs = Implicit (Elem x xs)

instance Implicit (Elem x (x ': xs)) where
  implicitly = Here

instance Implicit (Elem x xs) => Implicit (Elem x (y ': xs)) where
  implicitly = There implicitly
