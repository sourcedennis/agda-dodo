{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Dec where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Nullary using (Dec)
open import Relation.Unary using (Pred)


DecPred : {a ℓ : Level} {A : Set a}
  → Pred A ℓ → Set (a ⊔ ℓ)
DecPred P = ∀ x → Dec (P x)
