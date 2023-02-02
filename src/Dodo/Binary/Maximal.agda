{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Maximal where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary using (Trichotomous; tri<; tri≈; tri>)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Unary.Unique
open import Dodo.Binary.Equality


private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A : Set a


-- # Definitions #

maximal : {A : Set a}
  → Rel A ℓ
    --------------
  → Pred A (a ⊔ ℓ)
maximal r = λ x → ¬ (∃[ y ] r x y)


-- # Properties #

max-unique-tri : {≈ : Rel A ℓ₁} {< : Rel A ℓ₂}
  → Trichotomous ≈ <
  → Unique₁ ≈ (maximal <)
max-unique-tri tri {x} {y} ¬∃z[x<z] ¬∃z[y<z] with tri x y
... | tri< x<y _   _   = ⊥-elim (¬∃z[x<z] (y , x<y))
... | tri≈ _   x≈y _   = x≈y
... | tri> _   _   y<x = ⊥-elim (¬∃z[y<z] (x , y<x))


module _ {P : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  max-flips-⊆ : P ⊆₂ Q → maximal Q ⊆₁ maximal P
  max-flips-⊆ P⊆Q = ⊆: lemma
    where
    lemma : maximal Q ⊆₁' maximal P
    lemma x ¬∃zQxz (z , Pxz) = ¬∃zQxz (z , ⊆₂-apply P⊆Q Pxz)


module _ {P : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  max-preserves-⇔ : P ⇔₂ Q → maximal P ⇔₁ maximal Q
  max-preserves-⇔ = ⇔₁-sym ∘ ⇔₁-compose-⇔₂ max-flips-⊆ max-flips-⊆
