{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Trichotomous where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; subst; subst₂) renaming (sym to ≡-sym)
open import Level using (Level)
open import Function using (flip; _∘_; _∘₂_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; Irreflexive; Trichotomous; Tri; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using ([_])
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Binary.Equality
open import Dodo.Binary.Immediate
open import Dodo.Binary.Filter


-- # Definitions

tri-immˡ : {a ℓ₁ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂}
  → Trichotomous _≈_ R → {x y z : A}
  → immediate R x z → immediate R y z
    ---------------------------------
  → x ≈ y
tri-immˡ triR {x} {y} {z} (Rxz , ¬∃y) (Ryz , ¬∃x) with triR x y
... | tri<  Rxy x≢y ¬Ryx = ⊥-elim (¬∃y (y , Rxy , [ Ryz ]))
... | tri≈ ¬Rxy x≡y ¬Ryx = x≡y
... | tri> ¬Rxy x≢y  Ryx = ⊥-elim (¬∃x (x , Ryx , [ Rxz ]))


tri-immʳ : {a ℓ₁ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂}
  → Trichotomous _≈_ R → {x y z : A}
  → immediate R x y → immediate R x z
    ---------------------------------
  → y ≈ z
tri-immʳ triR {x} {y} {z} (Rxy , ¬∃z) (Rxz , ¬∃y) with triR y z
... | tri<  Ryz y≢z ¬Rzy = ⊥-elim (¬∃y (y , Rxy , [ Ryz ]))
... | tri≈ ¬Ryz y≡z ¬Rzy = y≡z
... | tri> ¬Ryz y≢z  Rzy = ⊥-elim (¬∃z (z , Rxz , [ Rzy ]))


tri-irreflexive : {a ℓ₁ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂}
  → Trichotomous _≈_ _<_
    --------------------
  → Irreflexive _≈_ _<_
tri-irreflexive triR {x} {y} x≈y x<y with triR x y
... | tri< x<y x≉y x≯y = x≉y x≈y
... | tri≈ x≮y x≈y x≯y = x≮y x<y
... | tri> x≮y x≉y x>y = x≉y x≈y


tri-flip : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → {x y : A}
  → Tri (R x y) (x ≡ y) (R y x)
    -------------------------------------
  → Tri (flip R x y) (x ≡ y) (flip R y x)
tri-flip (tri<  Rxy x≢y ¬Ryx) = tri> ¬Ryx x≢y  Rxy
tri-flip (tri≈ ¬Rxy x≡y ¬Ryx) = tri≈ ¬Ryx x≡y ¬Rxy
tri-flip (tri> ¬Rxy x≢y  Ryx) = tri<  Ryx x≢y ¬Rxy


trichotomous-flip : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → Trichotomous _≡_ R
    -------------------------
  → Trichotomous _≡_ (flip R)
trichotomous-flip {R = R} triR = tri-flip {R = R} ∘₂ triR
