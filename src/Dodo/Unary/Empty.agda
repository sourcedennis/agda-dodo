{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Empty where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product using (∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)


-- # Definitions

Empty₁ : ∀ {a ℓ : Level} {A : Set a} → Pred A ℓ → Set (a ⊔ ℓ)
Empty₁ {A = A} P = ∀ (x : A) → ¬ P x

NonEmpty₁ : ∀ {a ℓ : Level} {A : Set a} → Pred A ℓ → Set (a ⊔ ℓ)
NonEmpty₁ P = ∃[ x ] P x

¬₁_ : ∀ {a ℓ : Level} {A : Set a} → Pred A ℓ → Pred A ℓ
¬₁_ P x = ¬ P x
