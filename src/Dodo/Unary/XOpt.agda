{-# OPTIONS --without-K --safe #-}

-- | Exclusive option for predicates
module Dodo.Unary.XOpt where

-- Stdlib imports
open import Level using (Level)
open import Relation.Unary using (Pred)
-- Local imports
open import Dodo.Nullary.XOpt


private
  variable
    a ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a


-- # XOpt₂

XOptPred₂ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
XOptPred₂ {A = A} P Q = ∀ (x : A) → XOpt₂ (P x) (Q x)


-- # XOpt₃

XOptPred₃ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A ℓ₃ → Set _
XOptPred₃ {A = A} P Q R = ∀ (x : A) → XOpt₃ (P x) (Q x) (R x)
