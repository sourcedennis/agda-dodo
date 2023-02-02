{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Definition where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)


-- We rely upon the definitions from the standard library
open import Relation.Binary using (Rel; REL) public

-- And provide a few convenient shorthands


-- | A homogeneous binary relation, over types at universe level zero
Rel₀ : {a : Level} → Set a → Set (ℓsuc ℓzero ⊔ a)
Rel₀ A = Rel A ℓzero

-- | A heterogeneous binary relation, over types at universe level zero
REL₀ : {a b : Level} → Set a → Set b → Set (ℓsuc ℓzero ⊔ a ⊔ b)
REL₀ A B = REL A B ℓzero
