{-# OPTIONS --without-K --safe #-}

module Dodo.Nullary.Unique where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Level using (Level)

private
  variable
    a : Level

-- # Definitions

Unique : Set a → Set _
Unique A = ∀ (x y : A) → x ≡ y
