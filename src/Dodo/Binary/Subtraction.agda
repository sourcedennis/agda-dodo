{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Subtraction where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Binary using (REL)
-- Local imports
open import Dodo.Binary.Empty using (¬₂_)
open import Dodo.Binary.Intersection using (_∩₂_)


private
  variable
    a ℓ₁ ℓ₂ : Level
    A B : Set a


-- # Definitions

infixl 30 _\₂_

_\₂_ : REL A B ℓ₁ → REL A B ℓ₂ → REL A B (ℓ₁ ⊔ ℓ₂)
R \₂ Q = R ∩₂ (¬₂ Q)
