{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE StandaloneDeriving     #-}

-- |
-- Module      :  Rel.Interval
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Intervals and sets of intervals.
--

module Rel.Interval where

import           Algebra.PartialOrd
import           Control.Applicative
import           Control.Monad
import           Data.Maybe          (fromJust)
import           Data.Ratio
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Prelude             hiding (Enum (..))
import           Prelude.SafeEnum

-- Infinities
--------------------------------------------------------------------

data Inf a = NInf | Reg a | PInf
  deriving ( Eq, Ord, Show, Functor )

instance Applicative Inf where
  pure  = return
  (<*>) = ap

instance Monad Inf where
  return      = Reg
  PInf  >>= _ = PInf
  NInf  >>= _ = NInf
  Reg a >>= f = f a

instance Num a => Num (Inf a) where
  fromInteger    = Reg . fromInteger
  (+)            = liftA2 (+)
  (*)            = liftA2 (*)
  negate PInf    = NInf
  negate NInf    = PInf
  negate (Reg a) = Reg (negate a)
  abs NInf       = PInf
  abs PInf       = PInf
  abs (Reg a)    = Reg (abs a)
  signum PInf    = Reg 1
  signum NInf    = Reg (-1)
  signum (Reg a) = Reg (signum a)

instance (Eq a, Fractional a) => Fractional (Inf a) where
  PInf / PInf   = Reg (1/0) / (1/0)
  _    / PInf   = 0
  PInf / _      = PInf
  NInf / NInf   = Reg (1/0) / (1/0)
  _    / NInf   = Reg (1 / negate (1/0))
  NInf / _      = NInf
  Reg a / Reg 0 = PInf
  Reg a / Reg b = Reg (a / b)

  recip PInf    = 0
  recip NInf    = Reg (1 / negate (1/0))
  recip (Reg 0) = PInf
  recip (Reg a) = Reg (recip a)

  fromRational rat =
    Reg $ (fromIntegral $ numerator rat)
        / (fromIntegral $ denominator rat)

instance (Eq a, Floating a) => Floating (Inf a) where
  pi            = Reg pi

  exp PInf      = PInf
  exp NInf      = 0
  exp (Reg a)   = Reg (exp a)

  sqrt PInf     = PInf
  sqrt NInf     = Reg (0/0)
  sqrt (Reg a)  = Reg (sqrt a)

  log PInf      = PInf
  log NInf      = Reg (0/0)
  log (Reg a)   = Reg (log a)

  sin PInf      = Reg (0/0)
  sin NInf      = Reg (0/0)
  sin (Reg a)   = Reg (sin a)

  cos PInf      = Reg (0/0)
  cos NInf      = Reg (0/0)
  cos (Reg a)   = Reg (cos a)

  tan PInf      = Reg (0/0)
  tan NInf      = Reg (0/0)
  tan (Reg a)   = Reg (tan a)

  asin PInf     = Reg (0/0)
  asin NInf     = Reg (0/0)
  asin (Reg a)  = Reg (asin a)

  acos PInf     = Reg (0/0)
  acos NInf     = Reg (0/0)
  acos (Reg a)  = Reg (acos a)

  atan PInf     = pi/2
  atan NInf     = -pi/2
  atan (Reg a)  = Reg (atan a)

  sinh PInf     = PInf
  sinh NInf     = NInf
  sinh (Reg a)  = Reg (sinh a)

  cosh PInf     = PInf
  cosh NInf     = PInf
  cosh (Reg a)  = Reg (cosh a)

  tanh PInf     = 1
  tanh NInf     = -1
  tanh (Reg a)  = Reg (tanh a)

  asinh PInf    = PInf
  asinh NInf    = NInf
  asinh (Reg a) = Reg (asinh a)

  acosh PInf    = PInf
  acosh NInf    = Reg (0/0)
  acosh (Reg a) = Reg (acosh a)

  atanh PInf       = Reg (0/0)
  atanh NInf       = Reg (0/0)
  atanh (Reg 1)    = PInf
  atanh (Reg (-1)) = NInf
  atanh (Reg a)    = Reg (atanh a)

instance PartialOrd a => PartialOrd (Inf a) where
  leq NInf NInf       = False
  leq PInf PInf       = False
  leq NInf a          = True
  leq a    PInf       = True
  leq (Reg a) (Reg b) = leq a b

-- | Slightly violates the laws of 'UpwardEnum' as both @'PInf'
-- \`succeeds\` 'PInf'@ and @'NInf' \`succeeds\` 'NInf'@ both hold
-- violating the strict partial order requirement. The result of
-- this is that @'enumFrom' 'NInf'@ is @'repeat' 'NInf'@ and
-- @'enumFrom' 'PInf'@ is @'repeat' 'PInf'@. Further,
-- @'enumFromTo' n 'PInf'@ is @'enumFrom' n@.
instance UpwardEnum a => UpwardEnum (Inf a) where
  succ NInf = Just NInf
  succ PInf = Just PInf
  succ (Reg a) = case succ a of
                   Nothing -> Just PInf
                   Just b  -> Just (Reg b)

  succeeds PInf _          = True
  succeeds _    PInf       = False
  succeeds _    NInf       = True
  succeeds NInf _          = False
  succeeds (Reg a) (Reg b) = succeeds a b

instance DownwardEnum a => DownwardEnum (Inf a) where
  pred NInf = Just NInf
  pred PInf = Just PInf
  pred (Reg a) = case pred a of
                   Nothing -> Just NInf
                   Just b  -> Just (Reg b)

  precedes PInf _          = False
  precedes _    PInf       = True
  precedes _    NInf       = False
  precedes NInf _          = True
  precedes (Reg a) (Reg b) = precedes a b

instance Enum a => Enum (Inf a) where
  toEnum i         = Reg <$> toEnum i
  fromEnum (Reg i) = fromEnum i
  fromEnum _       = Nothing

instance Bounded (Inf a) where
  minBound = NInf
  maxBound = PInf


-- Intervals
--------------------------------------------------------------------

class Contains c a | c -> a where
  contains :: c -> a -> Bool

-- | An interval with point type @a@.
data I a = I (Inf a) (Inf a)
  deriving ( Eq )

-- | Lexicographic order. For containment order use 'leq'.
deriving instance Ord a => Ord (I a)

-- | Partial order by containment
instance Ord a => PartialOrd (I a) where
  leq (I b1 e1) (I b2 e2) =
    b1 <= b2 && e2 <= e1

before :: Ord a => I a -> I a -> Bool
before (I _ e1) (I b2 _) = e1 < b2

after :: Ord a => I a -> I a -> Bool
after a b = not (before a b)

meetsE :: (Eq a, UpwardEnum a) => I a -> I a -> Bool
meetsE (I b1 e1) (I b2 e2) =
  succ e1 == Just b2 || succ e2 == Just b1

meets :: (Eq a) => I a -> I a -> Bool
meets (I b1 e1) (I b2 e2) =
  e1 == b2 || e2 == b1

overlaps :: Ord a => I a -> I a -> Bool
overlaps (I b1 e1) (I b2 e2) = b1 <= e2 && b2 <= e1

merges :: (Ord a, UpwardEnum a) => I a -> I a -> Bool
merges a b = meets a b || overlaps a b

begins :: Eq a => I a -> I a -> Bool
begins (I b1 _) (I b2 _) = b1 == b2

ends :: Eq a => I a -> I a -> Bool
ends (I _ e1) (I _ e2) = e1 == e2

-- | Build an 'I' value from its endpoints.
interval :: Ord a => Inf a -> Inf a -> Maybe (I a)
interval a b | a <= b    = Just (I a b)
             | otherwise = Nothing

begin :: I a -> Inf a
begin (I b _) = b

end :: I a -> Inf a
end (I _ e) = e

count :: UpwardEnum a => I a -> Inf Int
count (I NInf _)          = PInf
count (I _ PInf)          = PInf
count (I (Reg a) (Reg b)) = Reg (length $ enumFromTo a b)

duration :: Num a => I a -> Inf a
duration (I b e) = e - b

-- pre and post are total because `succ`/`pred` on `Inf a` always
-- succeed.

pre :: DownwardEnum a => I a -> Inf a
pre = fromJust . pred . begin

post :: UpwardEnum a => I a -> Inf a
post = fromJust . succ . end

instance Ord a => Contains (I a) a where
  contains (I b e) a = b <= Reg a && Reg a <= e

unitInterval :: a -> I a
unitInterval a = I (Reg a) (Reg a)


-- Interval Sets
--------------------------------------------------------------------

-- | Interval sets are equivalence classes of sets of intervals.
-- Two sets of intervals, @a@ and @b@, are considered equivalent
-- when @forall x . contains a x <~> contains b x@ where @(<~>)@
-- means \"if and only if\". Without considering 'ISet's there
-- would be no closure under 'union' and 'intersection'.
newtype ISet a = ISet (Set (I a))

instance Ord a => Contains (ISet a) a where
  contains (ISet s) x = Set.fold go False s where
    go _ True  = True
    go i False = contains i x

-- | View the compact cannonical form of an 'ISet', the minimum
-- set of intervals in the equivalence class.
--
-- compact :: ISet -> [I a]

-- | View the expanded cannonical form of an 'ISet', the set of
-- all values which are contained in the 'ISet'.

unionIE :: (UpwardEnum a, Ord a) => I a -> I a -> ISet a
unionIE a@(I b1 e1) b@(I b2 e2)
  | meets a b = ISet (Set.singleton (I (min b1 b2) (max e1 e2)))
  | otherwise = ISet (Set.fromList [a, b])

unionI :: Ord a => I a -> I a -> ISet a
unionI a@(I b1 e1) b@(I b2 e2)
  | meets a b = ISet (Set.singleton (I (min b1 b2) (max e1 e2)))
  | otherwise = ISet (Set.fromList [a, b])

-- intersectionI :: Ord a => I a -> I a -> ISet a
-- intersectionI =

union :: Ord a => ISet a -> ISet a -> ISet a
union (ISet a) (ISet b) = ISet (Set.union a b)

-- intersection :: Ord a => ISet a -> ISet a -> ISet a
-- intersection =
