{-# OPTIONS --without-K --safe #-}

-- | Operations that ensure a cycle traverses a particular element
-- at most once.
module Dodo.Binary.Cycle where

-- Stdlib import
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _∷ʳ_; _++_)
-- Local imports
open import Dodo.Unary.Dec
open import Dodo.Binary.Transitive


-- # Definitions

-- | The given relation, with proofs that neither element equals `z`.
ExcludeRel : {a ℓ : Level} {A : Set a} → (R : Rel A ℓ) → (z : A) → Rel A (a ⊔ ℓ)
ExcludeRel R z x y = R x y × x ≢ z × y ≢ z

-- | A cycle of R which passes through `z` /exactly once/.
data PassCycle {a ℓ : Level} {A : Set a} (R : Rel A ℓ) (z : A) : Set (a ⊔ ℓ) where
  cycle₁ : R z z → PassCycle R z
  cycle₂ : {x : A} → x ≢ z → R z x → R x z → PassCycle R z
  cycleₙ : {x y : A} → R z x → TransClosure (ExcludeRel R z) x y → R y z → PassCycle R z


-- # Functions

-- | A cycle of a relation either /does not/ pass through an element `y`, or it
-- can be made to pass through `y` /exactly once/.
--
-- Note that if the original cycle passes `y` /more than once/, then only one
-- cycle of the multi-cycle through `y` may be taken.
divert-cycle : {a ℓ : Level} {A : Set a}
  → {R : Rel A ℓ}
  → {x : A}
  → TransClosure R x x
  → {y : A}
  → DecPred (_≡ y)
  → PassCycle R y ⊎ TransClosure (ExcludeRel R y) x x
divert-cycle {x = x} [ Rxx ] eq-xm with eq-xm x
... | yes refl = inj₁ (cycle₁ Rxx)
... | no  x≢y  = inj₂ [ ( Rxx , x≢y , x≢y ) ]
divert-cycle {A = A} {R = R} {x} ( Rxw ∷ R⁺wx ) {y} eq-dec = lemma Rxw R⁺wx
  where
  -- Chain that starts with `y`.
  --
  -- `Ryx` and `R⁺xz` are acculumators.
  lemma-incl : {x z : A} → R y x → TransClosure (ExcludeRel R y) x z → TransClosure R z y → PassCycle R y
  lemma-incl Ryx R⁺xz [ Rzy ] = cycleₙ Ryx R⁺xz Rzy
  lemma-incl Ryx R⁺xz (_∷_ {_} {w} Rzw R⁺wy) with eq-dec w
  lemma-incl Ryx R⁺xz (_∷_ {_} {w} Rzw R⁺wy) | yes refl = cycleₙ Ryx R⁺xz Rzw
  lemma-incl Ryx R⁺xz (_∷_ {_} {w} Rzw R⁺wy) | no  w≢y  =
    let z≢y = ⁺-lift-predʳ (proj₂ ∘ proj₂) R⁺xz
    in lemma-incl Ryx (R⁺xz ∷ʳ (Rzw , z≢y , w≢y)) R⁺wy

  -- First step of a chain that starts with `y`.
  lemma-incl₀ : {x : A} → R y x → TransClosure R x y → PassCycle R y
  lemma-incl₀ {x} Ryx R⁺xy with eq-dec x
  lemma-incl₀ {x} Ryx R⁺xy                   | yes refl = cycle₁ Ryx
  lemma-incl₀ {x} Ryx [ Rxy ]                | no  x≢y  = cycle₂ x≢y Ryx Rxy
  lemma-incl₀ {x} Ryx (_∷_ {_} {z} Rxz R⁺zy) | no x≢y with eq-dec z
  lemma-incl₀ {x} Ryx (_∷_ {x} {z} Rxz R⁺zy) | no x≢y | yes refl = cycle₂ x≢y Ryx Rxz
  lemma-incl₀ {x} Ryx (_∷_ {x} {z} Rxz R⁺zy) | no x≢y | no  z≢y  = lemma-incl Ryx [ Rxz , x≢y , z≢y ] R⁺zy

  -- Chain that does /not/ (yet) pass through `y`.
  lemma-excl : {z : A} → TransClosure (ExcludeRel R y) x z → TransClosure R z x → PassCycle R y ⊎ TransClosure (ExcludeRel R y) x x
  lemma-excl R⁺xz [ Rzx ] =
    let z≢y = ⁺-lift-predʳ (proj₂ ∘ proj₂) R⁺xz
        x≢y = ⁺-lift-predˡ (proj₁ ∘ proj₂) R⁺xz
    in inj₂ (R⁺xz ∷ʳ (Rzx , z≢y , x≢y))
  lemma-excl R⁺xz (_∷_ {_} {w} Rzw R⁺wx) with eq-dec w
  lemma-excl R⁺xz (_∷_ {_} {_} Rzw [ Rwx ])      | yes refl = inj₁ (cycleₙ Rwx R⁺xz Rzw)
  lemma-excl R⁺xz (_∷_ {_} {_} Rzw (Rwq ∷ R⁺qx)) | yes refl = inj₁ (lemma-incl₀ Rwq (R⁺qx ++ (⁺-map _ proj₁ R⁺xz) ∷ʳ Rzw))
  lemma-excl R⁺xz (_∷_ {_} {_} Rzw R⁺wx)         | no  w≢y =
    let z≢y = ⁺-lift-predʳ (proj₂ ∘ proj₂) R⁺xz
    in lemma-excl (R⁺xz ∷ʳ (Rzw , z≢y , w≢y)) R⁺wx
  
  lemma : {w : A} → R x w → TransClosure R w x → PassCycle R y ⊎ TransClosure (ExcludeRel R y) x x
  lemma {_} Rxw R⁺wx with eq-dec x
  lemma {_} Rxw R⁺wx           | yes refl = inj₁ (lemma-incl₀ Rxw R⁺wx)
  lemma {w} Rxw R⁺wx           | no  x≢y with eq-dec w
  lemma {_} Rxw [ Rwx ]        | no  x≢y | yes refl = inj₁ (cycle₂ x≢y Rwx Rxw)
  lemma {_} Rxw ( Rwz ∷ R⁺zx ) | no  x≢y | yes refl = inj₁ (lemma-incl₀ Rwz (R⁺zx ∷ʳ Rxw))
  lemma {_} Rxw R⁺wx           | no  x≢y | no  w≢y  = lemma-excl [ Rxw , x≢y , w≢y ] R⁺wx
