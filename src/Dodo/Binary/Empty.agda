{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Empty where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (REL; Rel)


-- # Definitions

-- | A predicate stating no inhabitants exist for the given relation
Empty₂ : ∀ {a b ℓ : Level} {A : Set a} {B : Set b} → REL A B ℓ → Set (a ⊔ b ⊔ ℓ)
Empty₂ {A = A} {B = B} r = ∀ (x : A) (y : B) → ¬ r x y

-- | Negation of a binary relation
¬₂_ : ∀ {a b ℓ : Level} {A : Set a} {B : Set b} → REL A B ℓ → REL A B ℓ
¬₂_ r x y = ¬ r x y
