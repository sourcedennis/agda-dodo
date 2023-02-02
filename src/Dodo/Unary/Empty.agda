{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Empty where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product using (∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)


private
  variable
    a ℓ : Level
    A : Set a
    

-- # Definitions

-- | The predicate is not satisfied by any element.
Empty₁ : {A : Set a} → Pred A ℓ → Set (a ⊔ ℓ)
Empty₁ {A = A} P = ∀ (x : A) → ¬ P x

-- | The predicate is satisfied by at least one element.
NonEmpty₁ : {A : Set a} → Pred A ℓ → Set (a ⊔ ℓ)
NonEmpty₁ P = ∃[ x ] P x

-- | Predicate negation
--
-- For any `x`, `x` satisfies `¬₁ P` iff it does not satisfy `P`.
¬₁_ : Pred A ℓ → Pred A ℓ
¬₁_ P x = ¬ P x
