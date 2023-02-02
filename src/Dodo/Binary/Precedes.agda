{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Precedes where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_)
open import Function using (id)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL; Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Local imports
open import Dodo.Binary.Transitive
open import Dodo.Binary.Immediate


private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a
    

-- # Definitions #

-- `¬ P x` before `¬ P y`
-- `P x`   before `¬ P y`
-- `P x`   before `P y`
⊤-Precedes-⊥ : REL (Pred A ℓ₁) (Rel A ℓ₂) _
⊤-Precedes-⊥ P R = ∀ {x y} → R x y → (P y → P x)

-- We could generalize `⊤-Precedes-⊥` to `Precedes` below:
--
-- Precedes : {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Rel A ℓ₃ → Set _
-- Precedes P Q R = ∀ {x y} → R x y → (P y → P x) × (Q x → Q y)
--
-- However, this is semantically a bit cumbersome, as P and Q are /not/ mutually exclusive.
-- Which means both P and Q may hold for an element.

-- # Operations #

⊤prec⊥-invert : {P : Pred A ℓ₁}
  → (R : Rel A ℓ₂)
  → ⊤-Precedes-⊥ P R
  → {x y : A}
  → R x y
  → ¬ P x
    ----------------
  → ¬ P y
⊤prec⊥-invert _ ⊤prec⊥ Rxy ¬Px Py = contraposition ¬Px id (⊤prec⊥ Rxy Py)


-- # Properties #

module _ {P : Pred A ℓ₁} {R : Rel A ℓ₂} where

  ⊤prec⊥-⁺ : ⊤-Precedes-⊥ P R → ⊤-Precedes-⊥ P (TransClosure R)
  ⊤prec⊥-⁺ Pprec¬P [ x∼y ]      Py = Pprec¬P x∼y Py
  ⊤prec⊥-⁺ Pprec¬P (x∼y ∷ y~⁺z) Py = Pprec¬P x∼y (⊤prec⊥-⁺ Pprec¬P y~⁺z Py)

  ⊤prec⊥-imm : ⊤-Precedes-⊥ P R → ⊤-Precedes-⊥ P (immediate R)
  ⊤prec⊥-imm Pprec¬P (x~y , ¬∃z) Py = Pprec¬P x~y Py
