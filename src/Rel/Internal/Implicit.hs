
-- |
-- Module      :  Rel.Internal.Implicit
-- Copyright   :  (C) 2014 Joseph Tel Abrahamson
-- License     :  BSD3
-- Maintainer  :  Joseph Abrahamson <me@jspha.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Implicitly available proof witnesses.
--
module Rel.Internal.Implicit where

-- | Typeclass indicating that a particular proof object can be
-- constructed implicitly via a type-level computation.
class Implicit p where
  implicitly :: p
