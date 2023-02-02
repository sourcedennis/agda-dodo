{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Definition where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)


-- We rely upon the definitions from the standard library
open import Relation.Unary using (Pred) public

-- And provide a few convenient shorthands


-- | A predicate, over types at universe level zero
Pred₀ : {a : Level} → Set a → Set (ℓsuc ℓzero ⊔ a)
Pred₀ A = Pred A ℓzero
