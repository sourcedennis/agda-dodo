{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Functional where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; REL)
-- Local imports
open import Dodo.Binary.Equality


private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    

-- # Definitions #

Functional : {A : Set a} {B : Set b}
  → Rel B ℓ₁
  → REL A B ℓ₂
    ---------------------
  → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Functional _≈_ r = ∀ x y₁ y₂ → r x y₁ → r x y₂ → y₁ ≈ y₂
-- The /explicit/ x, y₁, and y₂ are crucial. If they're implicit, Agda will attempt to
-- instantiate them when absent, which often fails to resolve. Not sure why.


-- # Operations #

functional-⊆₂ : {≈ : Rel A ℓ₁} {P : Rel A ℓ₂} {Q : Rel A ℓ₃}
  → P ⊆₂ Q → Functional ≈ Q → Functional ≈ P
functional-⊆₂ P⊆Q funcQ x y₁ y₂ Pxy₁ Pxy₂ = funcQ x y₁ y₂ (⊆₂-apply P⊆Q Pxy₁) (⊆₂-apply P⊆Q Pxy₂)
