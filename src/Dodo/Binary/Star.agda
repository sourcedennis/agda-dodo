{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Star where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A : Set a

*-predʳ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → P x → R x y → P y)
  → {x y : A}
  → Star R x y
  → P x
  → P y
*-predʳ f ε Px = Px
*-predʳ f (Rxz ◅ R*zy) Px = *-predʳ f R*zy (f Px Rxz)

*-predˡ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → P y → R x y → P x)
  → {x y : A}
  → Star R x y
  → P y
  → P x
*-predˡ f ε Py = Py
*-predˡ f (Rxz ◅ R*zy) Py = f (*-predˡ f R*zy Py) Rxz
