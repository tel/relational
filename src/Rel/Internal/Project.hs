{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- |
-- Module      :  Rel.Internal.Project
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Relational projection operations.
--
module Rel.Internal.Project ( 

    Project (..)
  , (:~:)
  , rearranged
  , (~=)
                   
) where

import           Control.Lens
import qualified Data.Set              as Set
import           GHC.Prim              (Constraint)
import           Rel.Internal.Elem
import           Rel.Internal.Implicit
import           Rel.Internal.Rel
import           Rel.Internal.Tup
import           Rel.Internal.Types

data Subset :: [k] -> [k] -> * where
  SubsetNil  :: Subset '[] xs
  SubsetCons :: Elem x ys
             -> Subset xs ys
             -> Subset (x ': xs) ys

type ISubset ts ss = Implicit (Subset ts ss)

instance Implicit (Subset '[] xs) where
  implicitly = SubsetNil

instance (IElem x ys, ISubset xs ys) => Implicit (Subset (x ': xs) ys) where
  implicitly = SubsetCons implicitly implicitly

type family   IsSubtype r1 r2 :: Constraint
type instance IsSubtype (Tup ss) (Tup ts) = ISubset ts ss
type instance IsSubtype (Rel ss) (Rel ts) = IsSubtype (Tup ss) (Tup ts)

class IsSubtype r1 r2 => Project r1 r2 where
  project :: r1 -> r2

instance Project (Tup xs) (Tup '[]) where
  project _ = Nil

instance
    (y ~ (sy ::: t), IElem y xs, Project (Tup xs) (Tup ys))
    => Project (Tup xs) (Tup (y ': ys))
    where
  project r = (r ^. inTup field) :+ project r where
    field = lookupField (implicitly :: Elem y xs) r

instance Ord (Tup xs) => Project (Rel xs) (Rel '[]) where
  project = over body (Set.map project)

instance
    ( Ord (Tup xs)
    , Ord (Tup ys)
    , Ord t
    , y ~ (sy ::: t)
    , IElem y xs
    , Project (Tup xs) (Tup ys))
    => Project (Rel xs) (Rel (y ': ys))
    where
  project = over body (Set.map project)

lookupField :: Elem x xs -> Tup xs -> x
lookupField Here      (_ :+ _)  = Attribute
lookupField (There p) (_ :+ xs) = lookupField p xs

-- | Isomorphism by projection
type r1 :~: r2 = (Project r1 r2, Project r2 r1)

-- | Conduct an isomoprhism via projection, in other words 
-- rearrange the attributes so as to match some other, 
-- isomorphic type. Works on relations and tuples.
rearranged :: (r1 :~: r2) => Iso' r1 r2
rearranged = iso project project

-- | Equality modulo 'project'ion. This can be used to check
-- propositional equivalence of 'Tup'les or 'Rel'ations and is
-- a super-relation to standard 'Eq' equality.
(~=) :: (Eq a, a :~: b) => a -> b -> Bool
x ~= y = x == project y
