{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeOperators    #-}

-- |
-- Module      :  Rel
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- An embedding of the Relational Model in Haskell.
module Rel ( 

  -- * Tuples
  
  -- | 'Tup'les are /facts/ stated in a relational model. They are
  -- (sadly, ordered) collections of named attribute values.
  -- Together they assert the truth of a proposition over those
  -- attributes. They are also, importantly, the atomic units which
  -- form 'Rel'ations.
  --
  -- If one has a desired 'Attribute' value then 'inTup' is a lens
  -- into any tuple over that 'Attribute', at that 'Attribute'.
    Tup (..)
  , inTup
  , IsTup

  -- ** Attributes
  
  -- | 'Attribute's are a bundled name and type together. They are
  -- represented at the type level as @(nm ':::' ty)@ where @nm@
  -- is the name of the 'Attribute' and @ty@ its type. All values
  -- of @(nm ':::' ty)@ are constructed identically using the
  -- 'Attribute' type constructor, thus if it's not obvious from
  -- context what the type of 'Attribute' is then the user should
  -- provide a type annotation.
  --
  -- @
  -- 'Attribute' :: \"foo\" ':::' Int
  -- @
  
  -- * Relations

  -- | 'Rel'ations are the core type in this package. They are
  -- essentially nothing more than 'Set's of 'Tup'les but due to
  -- the structure that provides we can define a number of
  -- interesting operations atop them. A 'Rel' containing @'Tup'
  -- rs@ is known as a @'Rel' rs@ or a 'Rel'ation of type @rs@.
  --
  -- One particular notion of a 'Rel' is that it is the
  -- characteristic function of a particular proposition. For
  -- instance, if we have a @('Rel' \'[\"name\" ':::' String, \"age\"
  -- ':::' Int])@ then we interpret the 'Tup'les inside of it as
  -- providing all of the true values of the proposition 
  -- /NAME is AGE years old/.

  , Rel, body

  -- ** Construction
  , tupRel, build

  -- *** Unsafe construction
  , insert
  
  -- ** Relational Operations
  
  -- *** Projection

  -- | Projection (supertype coercion) involves mapping
  -- a 'Rel'ation or 'Tup'le to another 'Rel'ation or 'Tup'le
  -- whose 'Attribute's are a subset of the source. Importantly
  -- projection does not require that the 'Attribute's are
  -- a /proper/ subset, thus we can 'project' in order to
  -- rearrange the order of attributes.

  , Project (..)
  , (:~:), rearranged, (~=)

  -- * Utilities

  , Only (..)
           
) where

import           Control.Lens
import qualified Data.Set             as Set
import           Rel.Internal.Project
import           Rel.Internal.Rel
import           Rel.Internal.Tup
import           Rel.Internal.Types

type S  = '[ "s#"     ::: Int
           , "sname"  ::: String
           , "status" ::: Int
           , "city"   ::: String
           ]

type SP = '[ "s#" ::: Int
           , "p#" ::: Int
           ]

type Sp = '[ "p#" ::: Int
           , "s#" ::: Int
           ]

tabS1 :: Rel S
tabS1 = build [ (1, "Smith", 20, "London")
              , (2, "Jones", 10, "Paris" )
              , (3, "Blake", 30, "Paris" )
              , (4, "Clark", 20, "London")
              , (5, "Adams", 30, "Athens")
              ]

tabSP1 :: Rel SP
tabSP1 = build (ungroup [ ( 1, [1..6]  )
                        , ( 2, [1..2]  )
                        , ( 3, [2]     )
                        , ( 4, [2,4,5] )
                        ])
  where ungroup = concatMap (\(i, vs) -> map (i,) vs)

tabSp1 :: Rel Sp
tabSp1 = build (ungroup [ ( 1, [1..6]  )
                        , ( 2, [1..2]  )
                        , ( 3, [2]     )
                        , ( 4, [2,4,5] )
                        ])
  where ungroup = concatMap (\(i, vs) -> map (,i) vs)
