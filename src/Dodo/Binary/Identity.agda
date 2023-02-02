{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Identity where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym)
open import Level using (Level; _⊔_)
open import Function.Base using (flip)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary using (Symmetric; Transitive; IsStrictTotalOrder)
-- Local imports
open import Dodo.Binary.Equality
open import Dodo.Binary.Composition
open import Dodo.Binary.Intersection
open import Dodo.Binary.Union
open import Dodo.Unary.Equality
open import Dodo.Unary.Intersection
open import Dodo.Unary.Union


private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A : Set a

-- # Definitions

-- | Identity relation over some set
--
-- Iff `P x` holds then `⦗ P ⦘ x x` holds.
⦗_⦘ : {A : Set a}
  → Pred A ℓ
    -------------
  → Rel A (a ⊔ ℓ)
⦗ p ⦘ x y = x ≡ y × p x


-- # Properties

⦗⦘-sym : {p : Pred A ℓ} → Symmetric ⦗ p ⦘
⦗⦘-sym (refl , px) = (refl , px)

⦗⦘-trans : {p : Pred A ℓ} → Transitive ⦗ p ⦘
⦗⦘-trans (refl , pi) (refl , _) = (refl , pi)

⦗⦘-flip : {p : Pred A ℓ} → ⦗ p ⦘ ⇔₂ flip ⦗ p ⦘
⦗⦘-flip = ⇔: (λ{_ _ → ⦗⦘-sym}) (λ{_ _ → ⦗⦘-sym})


-- # Operations

module _ {p : Pred A ℓ₁} where

  ⦗⦘-combine-⨾ : ⦗ p ⦘ ⨾ ⦗ p ⦘ ⇔₂ ⦗ p ⦘
  ⦗⦘-combine-⨾ = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : ⦗ p ⦘ ⨾ ⦗ p ⦘ ⊆₂' ⦗ p ⦘
    ⊆-proof _ _ ((refl , Px) ⨾[ x ]⨾ (refl , _)) = (refl , Px)
    ⊇-proof : ⦗ p ⦘ ⊆₂' ⦗ p ⦘ ⨾ ⦗ p ⦘
    ⊇-proof x _ (refl , Px) = (refl , Px) ⨾[ _ ]⨾ (refl , Px)


module _ {p : Pred A ℓ₁} {q : Pred A ℓ₂} where

  ⦗⦘-lift-⊆₂ : p ⊆₁ q → ⦗ p ⦘ ⊆₂ ⦗ q ⦘
  ⦗⦘-lift-⊆₂ (⊆: p⊆q) = ⊆: lemma
    where
    lemma : ⦗ p ⦘ ⊆₂' ⦗ q ⦘
    lemma x .x (refl , px) = (refl , p⊆q x px)

  ⦗⦘-unlift-⊆₂ : ⦗ p ⦘ ⊆₂ ⦗ q ⦘ → p ⊆₁ q
  ⦗⦘-unlift-⊆₂ (⊆: ⦗p⦘⊆⦗q⦘) = ⊆: lemma
    where
    lemma : p ⊆₁' q
    lemma x px = proj₂ (⦗p⦘⊆⦗q⦘ x x (refl , px))


module _ {p : Pred A ℓ₁} {q : Pred A ℓ₂} where

  ⦗⦘-lift : p ⇔₁ q → ⦗ p ⦘ ⇔₂ ⦗ q ⦘
  ⦗⦘-lift = ⇔₂-compose-⇔₁ ⦗⦘-lift-⊆₂ ⦗⦘-lift-⊆₂

  ⦗⦘-unlift : ⦗ p ⦘ ⇔₂ ⦗ q ⦘ → p ⇔₁ q
  ⦗⦘-unlift = ⇔₁-compose-⇔₂ ⦗⦘-unlift-⊆₂ ⦗⦘-unlift-⊆₂

  ⦗⦘-dist-∪ : ⦗ p ∪₁ q ⦘ ⇔₂ ⦗ p ⦘ ∪₂ ⦗ q ⦘
  ⦗⦘-dist-∪ = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : ⦗ p ∪₁ q ⦘ ⊆₂' ⦗ p ⦘ ∪₂ ⦗ q ⦘
    ⊆-proof _ _ (refl , inj₁ px) = inj₁ (refl , px)
    ⊆-proof _ _ (refl , inj₂ qx) = inj₂ (refl , qx)
    ⊇-proof : ⦗ p ⦘ ∪₂ ⦗ q ⦘ ⊆₂' ⦗ p ∪₁ q ⦘
    ⊇-proof _ _ (inj₁ (refl , px)) = (refl , inj₁ px)
    ⊇-proof _ _ (inj₂ (refl , qx)) = (refl , inj₂ qx)

  ⦗⦘-dist-∩ : ⦗ p ∩₁ q ⦘ ⇔₂ ⦗ p ⦘ ∩₂ ⦗ q ⦘
  ⦗⦘-dist-∩ = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : ⦗ p ∩₁ q ⦘ ⊆₂' ⦗ p ⦘ ∩₂ ⦗ q ⦘
    ⊆-proof x .x (refl , Px , Qx) = (refl , Px) , (refl , Qx)

    ⊇-proof : ⦗ p ⦘ ∩₂ ⦗ q ⦘ ⊆₂' ⦗ p ∩₁ q ⦘
    ⊇-proof x .x ((refl , Px) , (_ , Qx)) = refl , (Px , Qx)
