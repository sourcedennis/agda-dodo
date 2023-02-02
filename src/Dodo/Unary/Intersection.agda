{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Intersection where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_)
open import Level using (Level; _⊔_)
open import Function using (_∘₂_)
open import Data.Product using (_×_; _,_; swap; proj₁; proj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; REL)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Unary.Unique


private
  variable
    a ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    P Q R : Pred A ℓ

-- # Definitions

-- this has to bind stronger than _⇔₁_
infixr 6 _∩₁_

_∩₁_ :
    Pred A ℓ₁
  → Pred A ℓ₂
  → Pred A (ℓ₁ ⊔ ℓ₂)
_∩₁_ p q x = p x × q x


-- # Properties

module _ {P : Pred A ℓ} where

  ∩₁-idem : (P ∩₁ P) ⇔₁ P
  ∩₁-idem = ⇔: (λ _ → proj₁) ⊇-proof
    where
    ⊇-proof : P ⊆₁' (P ∩₁ P)
    ⊇-proof _ Px = (Px , Px)


∩₁-comm : (P ∩₁ Q) ⇔₁ (Q ∩₁ P)
∩₁-comm = ⇔: (λ _ → swap) (λ _ → swap)


module _ {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where
  
  ∩₁-assoc : (P ∩₁ (Q ∩₁ R)) ⇔₁ ((P ∩₁ Q) ∩₁ R)
  ∩₁-assoc = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : (P ∩₁ (Q ∩₁ R)) ⊆₁' ((P ∩₁ Q) ∩₁ R)
    ⊆-proof _ (Px , Qx , Rx) = ((Px , Qx) , Rx)
    ⊇-proof : ((P ∩₁ Q) ∩₁ R) ⊆₁' (P ∩₁ (Q ∩₁ R))
    ⊇-proof _ ((Px , Qx) , Rx) = (Px , Qx , Rx)


-- # Operations

-- ## Operations: General

∩₁-unique-pred :
    UniquePred P
  → UniquePred Q
  → UniquePred (P ∩₁ Q)
∩₁-unique-pred uniqueP uniqueQ x (Px₁ , Qx₁) (Px₂ , Qx₂)
  with uniqueP x Px₁ Px₂ | uniqueQ x Qx₁ Qx₂
... | refl | refl = refl


-- ## Operations: ⊆₁

∩₁-combine-⊆₁ : P ⊆₁ Q → P ⊆₁ R → P ⊆₁ (Q ∩₁ R)
∩₁-combine-⊆₁ (⊆: P⊆Q) (⊆: P⊆R) = ⊆: (λ x Px → (P⊆Q x Px , P⊆R x Px))

∩₁-introˡ-⊆₁ : (P ∩₁ Q) ⊆₁ P
∩₁-introˡ-⊆₁ = ⊆: (λ _ → proj₁)

∩₁-introʳ-⊆₁ : (P ∩₁ Q) ⊆₁ Q
∩₁-introʳ-⊆₁ = ⊆: (λ _ → proj₂)

∩₁-elimˡ-⊆₁ : P ⊆₁ (Q ∩₁ R) → P ⊆₁ R
∩₁-elimˡ-⊆₁ (⊆: P⊆[Q∩R]) = ⊆: (λ x Px → proj₂ (P⊆[Q∩R] x Px))

∩₁-elimʳ-⊆₁ : P ⊆₁ (Q ∩₁ R) → P ⊆₁ Q
∩₁-elimʳ-⊆₁ (⊆: P⊆[Q∩R]) = ⊆: (λ x Px → proj₁ (P⊆[Q∩R] x Px))


module _ {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where
    
  ∩₁-substˡ-⊆₁ : P ⊆₁ Q → (P ∩₁ R) ⊆₁ (Q ∩₁ R)
  ∩₁-substˡ-⊆₁ (⊆: P⊆Q) = ⊆: lemma
    where
    lemma : (P ∩₁ R) ⊆₁' (Q ∩₁ R)
    lemma x (Px , Rx) = (P⊆Q x Px , Rx)

  ∩₁-substʳ-⊆₁ : P ⊆₁ Q → (R ∩₁ P) ⊆₁ (R ∩₁ Q)
  ∩₁-substʳ-⊆₁ (⊆: P⊆Q) = ⊆: lemma
    where
    lemma : (R ∩₁ P) ⊆₁' (R ∩₁ Q)
    lemma x (Rx , Px) = (Rx , P⊆Q x Px)


-- ## Operations: ⇔₂

∩₁-substˡ : P ⇔₁ Q → (P ∩₁ R) ⇔₁ (Q ∩₁ R)
∩₁-substˡ = ⇔₁-compose ∩₁-substˡ-⊆₁ ∩₁-substˡ-⊆₁

∩₁-substʳ : P ⇔₁ Q → (R ∩₁ P) ⇔₁ (R ∩₁ Q)
∩₁-substʳ = ⇔₁-compose ∩₁-substʳ-⊆₁ ∩₁-substʳ-⊆₁
