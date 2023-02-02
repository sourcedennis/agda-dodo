{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Dec where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Nullary using (Dec)
open import Relation.Unary using (Pred)


private
  variable
    a ℓ : Level
    A : Set a
    

-- | Declares that the given predicate is decidable.
--
-- That is, for any given value (of type `A`), it either satisfies the
-- predicate or it does not.
DecPred : {A : Set a} → Pred A ℓ → Set (a ⊔ ℓ)
DecPred P = ∀ x → Dec (P x)
