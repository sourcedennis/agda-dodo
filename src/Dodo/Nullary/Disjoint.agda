{-# OPTIONS --without-K --safe #-}

module Dodo.Nullary.Disjoint where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)


private
  variable
    a b : Level


-- # Definitions

Disjoint : Set a → Set b → Set (a ⊔ b)
Disjoint A B = ¬ (A × B)
