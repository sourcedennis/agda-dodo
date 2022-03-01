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


-- # Definitions

-- | Acyclicity of a binary relation R: x R⁺ y → x ≠ y
--
-- Defined with an underlying equality (≈)
Acyclic : {a ℓ₁ ℓ₂ : Level} → {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Acyclic _≈_ _<_ = Irreflexive _≈_ (TransClosure _<_)


-- # Operations

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂} where

  -- | Any acyclic relation is also irreflexive
  Acyclic⇒Irreflexive : Acyclic _≈_ R → Irreflexive _≈_ R
  Acyclic⇒Irreflexive acyclicR x≈y Rxy = acyclicR x≈y [ Rxy ]


module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {_≈_ : Rel A ℓ₁} {P : Rel A ℓ₂} {Q : Rel A ℓ₃} where

  -- | If a relation is acyclic, then any subset of that relation is also acyclic
  acyclic-⊆₂ : Acyclic _≈_ Q → P ⊆₂ Q → Acyclic _≈_ P
  acyclic-⊆₂ acyclicQ P⊆Q x≈y P⁺ = acyclicQ x≈y (⊆₂-apply (⁺-preserves-⊆₂ P⊆Q) P⁺)


module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂} where

  -- | If a relation is acyclic, then its transitive closure is also acyclic
  ⁺-preserves-acyclic : Acyclic _≈_ R → Acyclic _≈_ (TransClosure R)
  ⁺-preserves-acyclic acR x≈y R⁺⁺xy = acR x≈y (⇔₂-apply-⊇₂ ⁺-idem R⁺⁺xy)
