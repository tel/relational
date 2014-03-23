{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  Rel.Internal.Rel
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The type of relations.
--
module Rel.Internal.Rel (

    Rel
  , body
  , tupRel
  , insert
  , build
               
) where

import           Control.Lens
import           Data.Set         (Set)
import qualified Data.Set         as Set
import           Rel.Internal.Tup

-- | Relations over a set of 'Tup'les.
data Rel rs = Rel (Set (Tup rs))

-- These instances cannot be proven decidable 
-- by Haskell, but they are...

deriving instance Eq   (Tup rs) => Eq   (Rel rs)
deriving instance Ord  (Tup rs) => Ord  (Rel rs)
deriving instance Show (Tup rs) => Show (Rel rs)

-- | A 'Lens' focusing on the set of 'Tup'les in this 'Rel'ation.
body :: Iso (Rel rs) (Rel rs') (Set (Tup rs)) (Set (Tup rs'))
body = iso (\(Rel x) -> x) Rel

-- | Build a singleton relation from a single tuple under no
-- constraints.
tupRel :: Tup rs -> Rel rs
tupRel tup = Rel (Set.singleton tup)

-- | Insert a new tuple into a relation unsafely. Use 
-- of 'insert' can violate the constraints of a relation.
insert :: Ord (Tup rs) => Tup rs -> Rel rs -> Rel rs
insert t = over body (Set.insert t)

-- | Common notation for building a relation under no constraints.
build :: (IsTup rs, Ord (Tup rs)) => [STup rs] -> Rel rs
build tups = body # (Set.fromList (map toTup tups))
