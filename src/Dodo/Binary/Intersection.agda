{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Intersection where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product as P
open import Data.Product using (_×_; _,_; swap; proj₁; proj₂)
open import Relation.Binary using (REL)
-- Local imports
open import Dodo.Binary.Equality


private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a
    P Q R : REL A B ℓ


-- # Definitions

-- this has to bind stronger than _⇔₂_
infixr 6 _∩₂_

_∩₂_ :
    REL A B ℓ₁
  → REL A B ℓ₂
  → REL A B (ℓ₁ ⊔ ℓ₂)
_∩₂_ P Q x y = P x y × Q x y


-- # Properties

∩₂-idem : R ∩₂ R  ⇔₂  R
∩₂-idem = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : R ∩₂ R  ⊆₂'  R
  ⊆-proof _ _ = proj₁
  ⊇-proof : R  ⊆₂'  R ∩₂ R
  ⊇-proof _ _ Rxy = (Rxy , Rxy)

∩₂-comm : P ∩₂ Q  ⇔₂  Q ∩₂ P
∩₂-comm = ⇔: (λ _ _ → swap) (λ _ _ → swap)

∩₂-assoc : P ∩₂ (Q ∩₂ R)  ⇔₂  (P ∩₂ Q) ∩₂ R
∩₂-assoc = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : P ∩₂ (Q ∩₂ R)  ⊆₂'  (P ∩₂ Q) ∩₂ R
  ⊆-proof _ _ (Pxy , (Qxy , Rxy)) = ((Pxy , Qxy) , Rxy)
  ⊇-proof : (P ∩₂ Q) ∩₂ R  ⊆₂'  P ∩₂ (Q ∩₂ R)
  ⊇-proof _ _ ((Pxy , Qxy) , Rxy) = (Pxy , (Qxy , Rxy))


-- # Operations

-- ## Operations: ⊆₂

∩₂-combine-⊆₂ : P ⊆₂ Q → P ⊆₂ R → P ⊆₂ (Q ∩₂ R)
∩₂-combine-⊆₂ (⊆: P⊆Q) (⊆: P⊆R) = ⊆: (λ x y Pxy → (P⊆Q x y Pxy , P⊆R x y Pxy))

∩₂-introˡ-⊆₂ : (P ∩₂ Q) ⊆₂ Q
∩₂-introˡ-⊆₂ = ⊆: λ _ _ → proj₂

∩₂-introʳ-⊆₂ : (P ∩₂ Q) ⊆₂ P
∩₂-introʳ-⊆₂ = ⊆: λ _ _ → proj₁

∩₂-elimˡ-⊆₂ : P ⊆₂ (Q ∩₂ R) → P ⊆₂ R
∩₂-elimˡ-⊆₂ (⊆: P⊆[Q∩R]) = ⊆: (λ x y Pxy → proj₂ (P⊆[Q∩R] x y Pxy))

∩₂-elimʳ-⊆₂ : P ⊆₂ (Q ∩₂ R) → P ⊆₂ Q
∩₂-elimʳ-⊆₂ (⊆: P⊆[Q∩R]) = ⊆: (λ x y Pxy → proj₁ (P⊆[Q∩R] x y Pxy))

∩₂-substˡ-⊆₂ : P ⊆₂ Q → (P ∩₂ R) ⊆₂ (Q ∩₂ R)
∩₂-substˡ-⊆₂ (⊆: P⊆Q) = ⊆: (λ x y → P.map₁ (P⊆Q x y))

∩₂-substʳ-⊆₂ : P ⊆₂ Q → (R ∩₂ P) ⊆₂ (R ∩₂ Q)
∩₂-substʳ-⊆₂ (⊆: P⊆Q) = ⊆: (λ x y → P.map₂ (P⊆Q x y))


-- ## Operations: ⇔₂

∩₂-substˡ : P ⇔₂ Q → (P ∩₂ R) ⇔₂ (Q ∩₂ R)
∩₂-substˡ = ⇔₂-compose ∩₂-substˡ-⊆₂ ∩₂-substˡ-⊆₂

∩₂-substʳ : P ⇔₂ Q → (R ∩₂ P) ⇔₂ (R ∩₂ Q)
∩₂-substʳ = ⇔₂-compose ∩₂-substʳ-⊆₂ ∩₂-substʳ-⊆₂
