{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Precedes where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL; Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Local imports
open import Dodo.Binary.Transitive
open import Dodo.Binary.Immediate


-- # Definitions #

-- `¬ P x` before `¬ P y`
-- `P x`   before `¬ P y`
-- `P x`   before `P y`
⊤-Precedes-⊥ : {a ℓ₁ ℓ₂ : Level} {A : Set a} → Pred A ℓ₁ → Rel A ℓ₂ → Set _
⊤-Precedes-⊥ P R = ∀ {x y} → R x y → (P y → P x)

-- We could generalize `⊤-Precedes-⊥` to `Precedes` below:
--
-- Precedes : {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Rel A ℓ₃ → Set _
-- Precedes P Q R = ∀ {x y} → R x y → (P y → P x) × (Q x → Q y)
--
-- However, this is semantically a bit cumbersome, as P and Q are /not/ mutually exclusive.
-- Which means both P and Q may hold for an element.


-- # Helpers #

private
  identity : {a : Level} → {A : Set a} → A → A
  identity x = x
  
  contrapositive : ∀ {a b : Level} {A : Set a} {B : Set b}
    → ( A → B ) → ( ¬ B → ¬ A )
  contrapositive f ¬b a = ¬b (f a)


-- # Operations #

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} (R : Rel A ℓ₂) where

  ⊤prec⊥-invert : ⊤-Precedes-⊥ P R → {x y : A} → R x y → ¬ P x → ¬ P y
  ⊤prec⊥-invert ⊤prec⊥ Rxy ¬Px Py = contrapositive ¬Px identity (⊤prec⊥ Rxy Py)


-- # Properties #

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {R : Rel A ℓ₂} where

  ⊤prec⊥-⁺ : ⊤-Precedes-⊥ P R → ⊤-Precedes-⊥ P (TransClosure R)
  ⊤prec⊥-⁺ Pprec¬P [ x∼y ]      Py = Pprec¬P x∼y Py
  ⊤prec⊥-⁺ Pprec¬P (x∼y ∷ y~⁺z) Py = Pprec¬P x∼y (⊤prec⊥-⁺ Pprec¬P y~⁺z Py)

  ⊤prec⊥-imm : ⊤-Precedes-⊥ P R → ⊤-Precedes-⊥ P (immediate R)
  ⊤prec⊥-imm Pprec¬P (x~y , ¬∃z) Py = Pprec¬P x~y Py
