{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Union where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Relation.Binary using (REL)
-- Local imports
open import Dodo.Binary.Equality


private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    P Q R : REL A B ℓ
    

-- # Definitions

-- this has to bind stronger than _⇔₂_
infixr 5 _∪₂_

_∪₂_ :
    REL A B ℓ₁
  → REL A B ℓ₂
  → REL A B (ℓ₁ ⊔ ℓ₂)
_∪₂_ p q x y = p x y ⊎ q x y


-- # Properties

module _ {R : REL A B ℓ} where

  ∪₂-idem : (R ∪₂ R) ⇔₂ R
  ∪₂-idem = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : (R ∪₂ R) ⊆₂' R
    ⊆-proof _ _ (inj₁ Rxy) = Rxy
    ⊆-proof _ _ (inj₂ Rxy) = Rxy
    
    ⊇-proof : R ⊆₂' (R ∪₂ R)
    ⊇-proof _ _ = inj₁


∪₂-comm : (P ∪₂ Q) ⇔₂ (Q ∪₂ P)
∪₂-comm = ⇔: (λ _ _ → swap) (λ _ _ → swap)


∪₂-assoc : (P ∪₂ Q) ∪₂ R  ⇔₂  P ∪₂ (Q ∪₂ R)
∪₂-assoc = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : (P ∪₂ Q) ∪₂ R  ⊆₂'  P ∪₂ (Q ∪₂ R)
  ⊆-proof _ _ (inj₁ (inj₁ Pxy)) = inj₁ Pxy
  ⊆-proof _ _ (inj₁ (inj₂ Qxy)) = inj₂ (inj₁ Qxy)
  ⊆-proof _ _ (inj₂ Rxy)        = inj₂ (inj₂ Rxy)
  
  ⊇-proof : P ∪₂ (Q ∪₂ R)  ⊆₂'  (P ∪₂ Q) ∪₂ R
  ⊇-proof _ _ (inj₁ Pxy)        = inj₁ (inj₁ Pxy)
  ⊇-proof _ _ (inj₂ (inj₁ Qxy)) = inj₁ (inj₂ Qxy)
  ⊇-proof _ _ (inj₂ (inj₂ Rxy)) = inj₂ Rxy


-- # Operations

-- ## Operations: ⊆₂

∪₂-combine-⊆₂ : P ⊆₂ Q → R ⊆₂ Q → (P ∪₂ R) ⊆₂ Q
∪₂-combine-⊆₂ (⊆: P⊆Q) (⊆: R⊆Q) = ⊆: (λ{x y → λ{(inj₁ Px) → P⊆Q x y Px; (inj₂ Rx) → R⊆Q x y Rx}})

∪₂-introˡ : P ⊆₂ (Q ∪₂ P)
∪₂-introˡ = ⊆: λ{_ _ → inj₂}

∪₂-introʳ : P ⊆₂ (P ∪₂ Q)
∪₂-introʳ = ⊆: λ{_ _ → inj₁}

∪₂-introˡ-⊆₂ : P ⊆₂ R → P ⊆₂ (Q ∪₂ R)
∪₂-introˡ-⊆₂ (⊆: P⊆R) = ⊆: (λ x y Pxy → inj₂ (P⊆R x y Pxy))

∪₂-introʳ-⊆₂ : P ⊆₂ Q → P ⊆₂ (Q ∪₂ R)
∪₂-introʳ-⊆₂ (⊆: P⊆Q) = ⊆: (λ x y Pxy → inj₁ (P⊆Q x y Pxy))

∪₂-elimˡ-⊆₂ : (P ∪₂ Q) ⊆₂ R → Q ⊆₂ R
∪₂-elimˡ-⊆₂ (⊆: [P∪Q]⊆R) = ⊆: (λ x y Qxy → [P∪Q]⊆R x y (inj₂ Qxy))

∪₂-elimʳ-⊆₂ : (P ∪₂ Q) ⊆₂ R → P ⊆₂ R
∪₂-elimʳ-⊆₂ (⊆: [P∪Q]⊆R) = ⊆: (λ x y Pxy → [P∪Q]⊆R x y (inj₁ Pxy))

∪₂-substˡ-⊆₂ : P ⊆₂ Q → (P ∪₂ R) ⊆₂ (Q ∪₂ R)
∪₂-substˡ-⊆₂ (⊆: P⊆Q) = ⊆: (λ{x y → λ{(inj₁ Pxy) → inj₁ (P⊆Q x y Pxy); (inj₂ Rxy) → inj₂ Rxy}})

∪₂-substʳ-⊆₂ : P ⊆₂ Q → (R ∪₂ P) ⊆₂ (R ∪₂ Q)
∪₂-substʳ-⊆₂ (⊆: P⊆Q) = ⊆: (λ{x y → λ{(inj₁ Rxy) → inj₁ Rxy; (inj₂ Pxy) → inj₂ (P⊆Q x y Pxy)}})


-- ## Operations: ⇔₂

∪₂-substˡ : P ⇔₂ Q → (P ∪₂ R) ⇔₂ (Q ∪₂ R)
∪₂-substˡ = ⇔₂-compose ∪₂-substˡ-⊆₂ ∪₂-substˡ-⊆₂

∪₂-substʳ : P ⇔₂ Q → (R ∪₂ P) ⇔₂ (R ∪₂ Q)
∪₂-substʳ = ⇔₂-compose ∪₂-substʳ-⊆₂ ∪₂-substʳ-⊆₂
