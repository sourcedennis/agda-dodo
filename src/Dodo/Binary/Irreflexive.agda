{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Irreflexive where

-- Stdlib imports
open import Level using (Level)
open import Relation.Binary using (Rel; Irreflexive)
-- Local imports
open import Dodo.Binary.Equality


module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {≈ : Rel A ℓ₁} {P : Rel A ℓ₂} {Q : Rel A ℓ₃} where

  irreflexive-⊆₂ : Irreflexive ≈ Q → P ⊆₂ Q → Irreflexive ≈ P
  irreflexive-⊆₂ irreflexiveQ P⊆Q x≈y Pxy = irreflexiveQ x≈y (⊆₂-apply P⊆Q Pxy)
