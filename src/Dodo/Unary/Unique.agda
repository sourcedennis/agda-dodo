{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Unique where

-- Stdlib imports
open import Level using (Level)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
-- Local imports
open import Dodo.Nullary.Unique


private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    

-- # Definitions #

-- | At most one element satisfies the predicate
Unique₁ : Rel A ℓ₁ → Pred A ℓ₂ → Set _
Unique₁ _≈_ P = ∀ {x y} → P x → P y → x ≈ y

-- | For every `x`, there exists at most one inhabitant of `P x`.
UniquePred : Pred A ℓ → Set _
UniquePred P = ∀ x → Unique (P x)

-- | For every `x`, there exists at most one parameter `v` for which `P v x` is true.
UniqueProp₁ : {A : Set ℓ} → Rel A ℓ₁ → {B : Set ℓ₁} → (A → Pred B ℓ₂) → Set _
UniqueProp₁ _≈_ f = ∀ {x} → Unique₁ _≈_ (λ v → f v x)
