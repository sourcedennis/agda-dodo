{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Acyclic where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Function using (flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive; Transitive; Symmetric)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_)
-- Local imports
open import Dodo.Binary.Equality
open import Dodo.Binary.Transitive


private
  variable
    a ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    

-- # Definitions

-- | Acyclicity of a binary relation R: x R⁺ y → x ≠ y
--
-- Defined with an underlying equality (≈)
Acyclic : Rel A ℓ₁ → Rel A ℓ₂ → Set _
Acyclic _≈_ _<_ = Irreflexive _≈_ (TransClosure _<_)


-- # Operations

-- | Any acyclic relation is also irreflexive
Acyclic⇒Irreflexive : {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂}
  → Acyclic _≈_ R → Irreflexive _≈_ R
Acyclic⇒Irreflexive acyclicR x≈y Rxy = acyclicR x≈y [ Rxy ]


-- | If a relation is acyclic, then any subset of that relation is also acyclic
acyclic-⊆₂ : {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂} {Q : Rel A ℓ₃}
  → Acyclic _≈_ Q → R ⊆₂ Q → Acyclic _≈_ R
acyclic-⊆₂ acyclicQ R⊆Q x≈y R⁺ = acyclicQ x≈y (⊆₂-apply (⁺-preserves-⊆₂ R⊆Q) R⁺)


-- | If a relation is acyclic, then its transitive closure is also acyclic
⁺-preserves-acyclic : {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂}
  → Acyclic _≈_ R → Acyclic _≈_ (TransClosure R)
⁺-preserves-acyclic acR x≈y R⁺⁺xy = acR x≈y (⇔₂-apply-⊇₂ ⁺-idem R⁺⁺xy)
