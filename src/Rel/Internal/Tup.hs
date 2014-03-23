{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  Rel.Internal.Tup
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The Tuple type.
--
module Rel.Internal.Tup ( 

    Tup (..)
  , inTup
  , IsTup (..)
               
) where

import           Control.Applicative
import           Control.Lens
import           Rel.Internal.Elem
import           Rel.Internal.Implicit
import           Rel.Internal.Types

-- | A tuple over an (unfortunately, ordered) set of 'Attribute's.
data Tup :: [*] -> * where
  Nil  :: Tup '[]
  (:+) :: t -> Tup vs -> Tup ((nm ::: t) ': vs)
infixr :+

instance (Show (STup rs), IsTup rs) => Show (Tup rs) where
  show = show . unTup

instance Eq (Tup '[]) where
  _ == _ = True

instance (Eq (Tup rs), Eq t) => Eq (Tup ((sy ::: t) ': rs)) where
  s :+ ss == t :+ ts = s == t && ss == ts

instance Ord (Tup '[]) where
  compare _ _ = EQ

-- | Lexicographic ordering
instance (Ord (Tup rs), Ord t) => Ord (Tup ((sy ::: t) ': rs)) where
  compare (s :+ ss) (t :+ ts) =
    case compare s t of
      EQ -> compare ss ts
      x  -> x

-- | Lens focusing on a particular element in a 'Tup'.
inTup :: forall r rs sy t g
      . (r ~ (sy ::: t), IElem r rs, Functor g)
      => r -> LensLike' g (Tup rs) t
inTup _ inj = go implicitly where
  go :: Elem r rr -> Tup rr -> g (Tup rr)
  go Here (x :+ xs) = (:+ xs) <$> inj x
  go (There p) (x :+ xs) = (x :+) <$> go p xs

class IsTup t where
  type STup t
  unTup :: Tup t -> STup t
  toTup :: STup t -> Tup t

instance IsTup '[] where
  type STup '[] = ()
  unTup  _ = ()
  toTup () = Nil

instance IsTup '[sy ::: r] where
  type STup '[sy ::: r] = Only r
  unTup (v :+ Nil) = Only v
  toTup (Only v)   = v :+ Nil

instance IsTup '[sy1 ::: r, sy2 ::: s] where
  type STup '[sy1 ::: r, sy2 ::: s] = (r, s)
  unTup (v1 :+ v2 :+ Nil) = (v1, v2)
  toTup (v1, v2)   = v1 :+ v2 :+ Nil

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3] = (t1, t2, t3)
  unTup (v1 :+ v2 :+ v3 :+ Nil) = (v1, v2, v3)
  toTup (v1, v2, v3)   = v1 :+ v2 :+ v3 :+ Nil

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4] = (t1, t2, t3, t4)
  unTup (v1 :+ v2 :+ v3 :+ v4 :+ Nil) = (v1, v2, v3, v4)
  toTup (v1, v2, v3, v4)   = v1 :+ v2 :+ v3 :+ v4 :+ Nil

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5] = (t1, t2, t3, t4,t5)
  unTup (v1 :+ v2 :+ v3 :+ v4 :+v5 :+ Nil) = (v1, v2, v3, v4,v5)
  toTup (v1, v2, v3, v4,v5) = (v1 :+ v2 :+ v3 :+ v4 :+v5 :+ Nil)

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5,sy6 ::: t6] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5,sy6 ::: t6] = (t1, t2, t3, t4, t5,t6)
  unTup (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+v6 :+ Nil) = (v1, v2, v3, v4, v5, v6)
  toTup (v1, v2, v3, v4, v5, v6) = (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+v6 :+ Nil)

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5, sy6 ::: t6,sy7 ::: t7] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5, sy6 ::: t6,sy7 ::: t7] = (t1, t2, t3, t4, t5, t6, t7)
  unTup (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+ v6 :+v7 :+ Nil) = (v1, v2, v3, v4, v5, v6, v7)
  toTup (v1, v2, v3, v4, v5, v6, v7) = (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+ v6 :+v7 :+ Nil)

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5, sy6 ::: t6, sy7 ::: t7,sy8 ::: t8] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5, sy6 ::: t6, sy7 ::: t7,sy8 ::: t8] = (t1, t2, t3, t4, t5, t6, t7, t8)
  unTup (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+ v6 :+ v7 :+v8 :+ Nil) = (v1, v2, v3, v4, v5, v6, v7, v8)
  toTup (v1, v2, v3, v4, v5, v6, v7, v8) = (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+ v6 :+ v7 :+v8 :+ Nil)

instance IsTup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5, sy6 ::: t6, sy7 ::: t7, sy8 ::: t8,sy9 ::: t9] where
  type STup '[sy1 ::: t1, sy2 ::: t2, sy3 ::: t3, sy4 ::: t4, sy5 ::: t5, sy6 ::: t6, sy7 ::: t7, sy8 ::: t8,sy9 ::: t9] = (t1, t2, t3, t4, t5, t6, t7, t8, t9)
  unTup (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+ v6 :+ v7 :+ v8 :+v9 :+ Nil) = (v1, v2, v3, v4, v5, v6, v7, v8, v9)
  toTup (v1, v2, v3, v4, v5, v6, v7, v8, v9) = (v1 :+ v2 :+ v3 :+ v4 :+ v5 :+ v6 :+ v7 :+ v8 :+v9 :+ Nil)

