{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Reflexive where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary.Construct.Closure.Reflexive using (ReflClosure; [_]; refl)

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A : Set a

?-predʳ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → R x y → P y)
  → {x y : A}
  → ReflClosure R x y
  → P x
  → P y
?-predʳ f refl    Px = Px
?-predʳ f [ Rxy ] Px = f Rxy

?-predˡ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → R x y → P x)
  → {x y : A}
  → ReflClosure R x y
  → P y
  → P x
?-predˡ f refl    Py = Py
?-predˡ f [ Rxy ] Py = f Rxy
