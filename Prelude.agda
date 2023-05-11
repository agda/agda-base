------------------------------------------------------------------------
-- From stdlib-meta
--
-- Prelude
------------------------------------------------------------------------

module Prelude where

open import Level renaming (_⊔_ to _⊔ˡ_; suc to sucˡ; zero to zeroˡ) public
open import Function public

open import Data.Bool public -- hiding (_≟_; _≤_; _≤?_; _<_; _<?_) public
open import Data.Empty public
open import Data.List hiding (ap; fromMaybe; map; zip; zipWith) public -- ; align; alignWith) public
open import Data.Maybe hiding (_>>=_; fromMaybe; map; zip; zipWith) public -- ; align; alignWith) public
open import Data.Unit public -- hiding (_≟_; decSetoid)
open import Data.Sum hiding (assocʳ; assocˡ; map; map₁; map₂; reduce; swap) public
open import Data.Product hiding (assocʳ; assocˡ; map; map₁; map₂; swap) public
open import Data.Nat hiding (_≤_; _<_; _≤ᵇ_; _≡ᵇ_) public -- ; _≟_; _≤?_; _<?_) public
open import Data.String using (String; _<+>_) public

-- open import Relation.Binary.PropositionalEquality hiding (preorder; setoid; [_]; module ≡-Reasoning; decSetoid) public
