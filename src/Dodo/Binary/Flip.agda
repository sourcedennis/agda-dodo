{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Flip where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Function.Base using (flip)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Symmetric)
-- Local imports
open import Dodo.Binary.Equality


-- # Operations

-- ## Operations: ⊆₂

module _ {a b ℓ₁ ℓ₂ : Level} {A : Set a} {B : Set b}
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} where

  flip-⊆₂ : P ⊆₂ Q → flip P ⊆₂ flip Q
  flip-⊆₂ (⊆: P⊆Q) = ⊆: (flip P⊆Q)


module _ {a ℓ₁ : Level} {A : Set a} {P : Rel A ℓ₁} where

  flip-sym-⊆₂ : Symmetric P → P ⊆₂ flip P
  flip-sym-⊆₂ symP = ⊆: (λ _ _ → symP)
  

-- ## Operations: ⇔₂

module _ {a b ℓ₁ ℓ₂ : Level} {A : Set a} {B : Set b}
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} where
    
  flip-⇔₂ : P ⇔₂ Q → flip P ⇔₂ flip Q
  flip-⇔₂ = ⇔₂-compose flip-⊆₂ flip-⊆₂


module _ {a ℓ₁ : Level} {A : Set a} {P : Rel A ℓ₁} where

  flip-sym-⇔₂ : Symmetric P → P ⇔₂ flip P
  flip-sym-⇔₂ symP = ⇔₂-intro (flip-sym-⊆₂ symP) (flip-sym-⊆₂ symP)
