{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Subtraction where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Binary using (REL)
-- Local imports
open import Dodo.Binary.Empty using (¬₂_)
open import Dodo.Binary.Intersection using (_∩₂_)


-- # Definitions

infixl 30 _\₂_

_\₂_ : {a b ℓ₀ ℓ₁ : Level} {A : Set a} {B : Set b} → REL A B ℓ₀ → REL A B ℓ₁ → REL A B (ℓ₀ ⊔ ℓ₁)
_\₂_ R Q = R ∩₂ (¬₂ Q)
