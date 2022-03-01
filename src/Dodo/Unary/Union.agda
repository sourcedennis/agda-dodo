{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Union where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong)
open import Level using (Level; _⊔_)
open import Function using (_∘_; _∘₂_)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Unary using (Pred)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Unary.Unique
open import Dodo.Unary.Disjoint


-- # Definitions

infixl 30 _∪₁_

_∪₁_ : {a ℓ₁ ℓ₂ : Level} {A : Set a}
  → Pred A ℓ₁
  → Pred A ℓ₂
  → Pred A (ℓ₁ ⊔ ℓ₂)
_∪₁_ p q x = p x ⊎ q x


-- # Properties

module _ {a ℓ : Level} {A : Set a} {R : Pred A ℓ} where

  ∪₁-idem : (R ∪₁ R) ⇔₁ R
  ∪₁-idem = ⇔: ⊆-proof (λ _ → inj₁)
    where
    ⊆-proof : (R ∪₁ R) ⊆₁' R
    ⊆-proof _ (inj₁ Rx) = Rx
    ⊆-proof _ (inj₂ Rx) = Rx


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} where

  ∪₁-comm : (P ∪₁ Q) ⇔₁ (Q ∪₁ P)
  ∪₁-comm = ⇔: (λ _ → swap) (λ _ → swap)


module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ∪₁-assoc : (P ∪₁ Q) ∪₁ R ⇔₁ P ∪₁ (Q ∪₁ R)
  ∪₁-assoc = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : ((P ∪₁ Q) ∪₁ R) ⊆₁' (P ∪₁ (Q ∪₁ R))
    ⊆-proof _ (inj₁ (inj₁ Px)) = inj₁ Px
    ⊆-proof _ (inj₁ (inj₂ Qx)) = inj₂ (inj₁ Qx)
    ⊆-proof _ (inj₂ Rx)        = inj₂ (inj₂ Rx)
    ⊇-proof : (P ∪₁ (Q ∪₁ R)) ⊆₁' ((P ∪₁ Q) ∪₁ R)
    ⊇-proof _ (inj₁ Px)        = inj₁ (inj₁ Px)
    ⊇-proof _ (inj₂ (inj₁ Qx)) = inj₁ (inj₂ Qx)
    ⊇-proof _ (inj₂ (inj₂ Rx)) = inj₂ Rx


-- # Operations

-- ## Operations: General

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} where
    
  ∪₁-unique-pred :
      Disjoint₁ P Q
    → UniquePred P
    → UniquePred Q
    → UniquePred (P ∪₁ Q)
  ∪₁-unique-pred _     uniqueP _       x (inj₁ Px₁) (inj₁ Px₂) = cong inj₁ (uniqueP x Px₁ Px₂)
  ∪₁-unique-pred disPQ _       _       x (inj₁ Px)  (inj₂ Qx)  = ⊥-elim (disPQ x (Px , Qx))
  ∪₁-unique-pred disPQ _       _       x (inj₂ Qx)  (inj₁ Px)  = ⊥-elim (disPQ x (Px , Qx))
  ∪₁-unique-pred _     _       uniqueQ x (inj₂ Qx₁) (inj₂ Qx₂) = cong inj₂ (uniqueQ x Qx₁ Qx₂)


-- ## Operations: ⊆₁

module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ∪₁-combine-⊆₁ : P ⊆₁ Q → R ⊆₁ Q → (P ∪₁ R) ⊆₁ Q
  ∪₁-combine-⊆₁ (⊆: P⊆Q) (⊆: R⊆Q) = ⊆: lemma
    where
    lemma : (P ∪₁ R) ⊆₁' Q
    lemma x (inj₁ Px) = P⊆Q x Px
    lemma x (inj₂ Rx) = R⊆Q x Rx
    

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} where

  ∪₁-introˡ : P ⊆₁ (Q ∪₁ P)
  ∪₁-introˡ = ⊆: λ{_ → inj₂}

  ∪₁-introʳ : P ⊆₁ (P ∪₁ Q)
  ∪₁-introʳ = ⊆: λ{_ → inj₁}


module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ∪₁-introˡ-⊆₁ : P ⊆₁ R → P ⊆₁ (Q ∪₁ R)
  ∪₁-introˡ-⊆₁ (⊆: P⊆R) = ⊆: (inj₂ ∘₂ P⊆R)

  ∪₁-introʳ-⊆₁ : P ⊆₁ Q → P ⊆₁ (Q ∪₁ R)
  ∪₁-introʳ-⊆₁ (⊆: P⊆Q) = ⊆: (inj₁ ∘₂ P⊆Q)

  ∪₁-elimˡ-⊆₁ : (P ∪₁ Q) ⊆₁ R → Q ⊆₁ R
  ∪₁-elimˡ-⊆₁ (⊆: [P∪Q]⊆R) = ⊆: (λ x → [P∪Q]⊆R x ∘ inj₂)

  ∪₁-elimʳ-⊆₁ : (P ∪₁ Q) ⊆₁ R → P ⊆₁ R
  ∪₁-elimʳ-⊆₁ (⊆: [P∪Q]⊆R) = ⊆: (λ x → [P∪Q]⊆R x ∘ inj₁)


module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ∪₁-substˡ-⊆₁ : P ⊆₁ Q → (P ∪₁ R) ⊆₁ (Q ∪₁ R)
  ∪₁-substˡ-⊆₁ (⊆: P⊆Q) = ⊆: lemma
    where
    lemma : (P ∪₁ R) ⊆₁' (Q ∪₁ R)
    lemma x (inj₁ Px) = inj₁ (P⊆Q x Px)
    lemma x (inj₂ Rx) = inj₂ Rx

  ∪₁-substʳ-⊆₁ : P ⊆₁ Q → (R ∪₁ P) ⊆₁ (R ∪₁ Q)
  ∪₁-substʳ-⊆₁ (⊆: P⊆Q) = ⊆: lemma
    where
    lemma : (R ∪₁ P) ⊆₁' (R ∪₁ Q)
    lemma x (inj₁ Rx) = inj₁ Rx
    lemma x (inj₂ Px) = inj₂ (P⊆Q x Px)


-- ## Operations: ⇔₂

module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ∪₁-substˡ : P ⇔₁ Q → (P ∪₁ R) ⇔₁ (Q ∪₁ R)
  ∪₁-substˡ = ⇔₁-compose ∪₁-substˡ-⊆₁ ∪₁-substˡ-⊆₁

  ∪₁-substʳ : P ⇔₁ Q → (R ∪₁ P) ⇔₁ (R ∪₁ Q)
  ∪₁-substʳ = ⇔₁-compose ∪₁-substʳ-⊆₁ ∪₁-substʳ-⊆₁
