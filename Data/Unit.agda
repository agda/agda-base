------------------------------------------------------------------------
-- From the Agda standard library
--
-- The unit type
------------------------------------------------------------------------

module Data.Unit where

------------------------------------------------------------------------
-- Re-export contents of base module

open import Data.Unit.Base public

Unit = ⊤

{-
------------------------------------------------------------------------
-- Re-export query operations

open import Data.Unit.Properties public
  using (_≟_)
-}
