{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Dec where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Nullary using (Dec)
open import Relation.Binary using (REL)


private
  variable
    a b ℓ : Level


DecRel : {A : Set a} {B : Set b} → REL A B ℓ → Set (a ⊔ b ⊔ ℓ)
DecRel R = ∀ x y → Dec (R x y)
