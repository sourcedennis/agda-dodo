{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Flip where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Function.Base using (flip)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Symmetric)
-- Local imports
open import Dodo.Binary.Equality


private
  variable
    a b ℓ₁ ℓ₂ : Level
    A B : Set a

-- # Operations

-- ## Operations: ⊆₂

flip-⊆₂ : {P : REL A B ℓ₁} {Q : REL A B ℓ₂} → P ⊆₂ Q → flip P ⊆₂ flip Q
flip-⊆₂ (⊆: P⊆Q) = ⊆: (flip P⊆Q)

flip-sym-⊆₂ : {P : Rel A ℓ₁} → Symmetric P → P ⊆₂ flip P
flip-sym-⊆₂ symP = ⊆: (λ _ _ → symP)


-- ## Operations: ⇔₂
 
flip-⇔₂ : {P : REL A B ℓ₁} {Q : REL A B ℓ₂} → P ⇔₂ Q → flip P ⇔₂ flip Q
flip-⇔₂ = ⇔₂-compose flip-⊆₂ flip-⊆₂

flip-sym-⇔₂ : {P : Rel A ℓ₁} → Symmetric P → P ⇔₂ flip P
flip-sym-⇔₂ symP = ⇔₂-intro (flip-sym-⊆₂ symP) (flip-sym-⊆₂ symP)
