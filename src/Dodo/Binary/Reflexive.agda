{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Reflexive where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL; Transitive)
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


trans-?ʳ : {R : Rel A ℓ₁}
  → Transitive R
  → {x y z : A}
  → R x y
  → ReflClosure R y z
  → R x z
trans-?ʳ trans-R Rxz refl    = Rxz
trans-?ʳ trans-R Rxy [ Ryz ] = trans-R Rxy Ryz

trans-?ˡ : {R : Rel A ℓ₁}
  → Transitive R
  → {x y z : A}
  → ReflClosure R x y
  → R y z
  → R x z
trans-?ˡ trans-R refl    Ryz = Ryz
trans-?ˡ trans-R [ Rxy ] Ryz = trans-R Rxy Ryz

trans-? : {R : Rel A ℓ₁}
  → Transitive R
  → {x y z : A}
  → ReflClosure R x y
  → ReflClosure R y z
  → ReflClosure R x z
trans-? trans-R refl    refl    = refl
trans-? trans-R refl    [ Ryz ] = [ Ryz ]
trans-? trans-R [ Rxy ] refl    = [ Rxy ]
trans-? trans-R [ Rxy ] [ Ryz ] = [ trans-R Rxy Ryz ]
