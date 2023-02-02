{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Disjoint where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Empty using (⊥)
open import Relation.Unary using (Pred)
-- Local imports
open import Dodo.Unary.Empty
open import Dodo.Unary.Intersection


private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a


-- # Definitions

Disjoint₁ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
Disjoint₁ P Q = Empty₁ (P ∩₁ Q)
