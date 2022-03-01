{-# OPTIONS --without-K --safe #-}

module Dodo.Nullary.Disjoint where

-- Stdlib imports
open import Level using (Level)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)


-- # Definitions

Disjoint : ∀ {a b : Level} (A : Set a) (B : Set b) → Set _
Disjoint A B = ¬ (A × B)
