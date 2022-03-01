{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Product where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Function using (flip)
open import Data.Product using (_×_; _,_; map₁; map₂)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (REL; Rel)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Binary.Equality
open import Dodo.Binary.Domain
open import Dodo.Binary.Composition


infix 40 _×₂_

_×₂_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  → Pred A ℓ₁
  → Pred B ℓ₂
    -----------------
  → REL A B (ℓ₁ ⊔ ℓ₂)
_×₂_ P Q x y = P x × Q y


-- ## Operations: ×₂ ##

module _ {a b ℓ₁ ℓ₂ : Level} {A : Set a} {B : Set b}
    {d : Pred A ℓ₁} {r : Pred B ℓ₂} where

  ×₂-dom : ∀ {x : A} {y : B} → ( d ×₂ r ) x y → d x
  ×₂-dom (dx , ry) = dx
  
  ×₂-codom : ∀ {x : A} {y : B} → ( d ×₂ r ) x y → r y
  ×₂-codom (dx , ry) = ry

  ×₂-flip : ∀ {x : A} {y : B} → ( d ×₂ r ) x y → ( r ×₂ d ) y x
  ×₂-flip (dx , ry) = (ry , dx)
  

module _ {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b}
    {d₁ : Pred A ℓ₁} {d₂ : Pred A ℓ₂} {r₁ : Pred B ℓ₃} {r₂ : Pred B ℓ₄} where
    
  ×₂-lift : ( d₁ ⊆₁ d₂ ) → ( r₁ ⊆₁ r₂ ) → d₁ ×₂ r₁ ⊆₂ d₂ ×₂ r₂
  ×₂-lift f g = ⊆: lemma
    where
    lemma : d₁ ×₂ r₁ ⊆₂' d₂ ×₂ r₂
    lemma x y (d₁x , r₁y) = (⊆₁-apply f d₁x , ⊆₁-apply g r₁y)


module _ {a b ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} {B : Set b} {R : REL A B ℓ₁}
    {d : Pred A ℓ₂} {r : Pred B ℓ₃} where

  ×₂-applyˡ : R ⊆₂ ( d ×₂ r ) → {x : A} {y : B} → R x y → d x
  ×₂-applyˡ R⊆₂d×r Rxy = ×₂-dom {d = d} {r = r} (⊆₂-apply R⊆₂d×r Rxy)

  ×₂-apply-dom : R ⊆₂ (d ×₂ r) → {x : A} → x ∈ dom R → d x
  ×₂-apply-dom R⊆d×r (y , Rxy) = ×₂-applyˡ R⊆d×r Rxy

  ×₂-applyʳ : R ⊆₂ ( d ×₂ r ) → {x : A} {y : B} → R x y → r y
  ×₂-applyʳ R⊆₂d×r Rxy = ×₂-codom {d = d} {r = r} (⊆₂-apply R⊆₂d×r Rxy)

  ×₂-apply-codom : R ⊆₂ (d ×₂ r) → {y : B} → y ∈ codom R → r y
  ×₂-apply-codom R⊆d×r (x , Rxy) = ×₂-applyʳ R⊆d×r Rxy


module _ {a b ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} {B : Set b}
    {Q : REL A B ℓ₁} {d : A → Set ℓ₂} {r : B → Set ℓ₃} where

  ×₂-flip-⊆₂ : Q ⊆₂ d ×₂ r → flip Q ⊆₂ r ×₂ d
  ×₂-flip-⊆₂ (⊆: Q⊆×) = ⊆: lemma
    where
    lemma : flip Q ⊆₂' r ×₂ d
    lemma x y Qyx with Q⊆× y x Qyx
    ... | (dy , rx) = (rx , dy)


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {R : Rel A ℓ₁} {P : Pred A ℓ₂} where
    
  ×₂-lift-udr :
      udr R ⊆₁ P
      -----------
    → R ⊆₂ P ×₂ P
  ×₂-lift-udr udrR⊆P = ⊆: lemma
    where
    lemma : R ⊆₂' P ×₂ P
    lemma x y Rxy = ⊆₁-apply udrR⊆P (take-udrˡ R Rxy) , ⊆₁-apply udrR⊆P (take-udrʳ R Rxy)


module _ {a b ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} {B : Set b}
    {R : REL A B ℓ₁} {P : Pred A ℓ₂} {Q : Pred B ℓ₃} where

  ×₂-lift-dom :
      dom R ⊆₁ P
    → codom R ⊆₁ Q
      ------------
    → R ⊆₂ P ×₂ Q
  ×₂-lift-dom (⊆: dom⊆P) (⊆: codom⊆Q) = ⊆: lemma
    where
    lemma : R ⊆₂' P ×₂ Q
    lemma x y Rxy = (dom⊆P x (take-dom R Rxy) , codom⊆Q y (take-codom R Rxy))
  

module _ {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b}
    {Q : REL A B ℓ₁} {d₁ : Pred A ℓ₂} {d₂ : Pred A ℓ₃} {r : B → Set ℓ₄} where

  ×₂-⊆ˡ :
      d₁ ⊆₁ d₂
      ------------------
    → d₁ ×₂ r ⊆₂ d₂ ×₂ r
  ×₂-⊆ˡ d₁⊆d₂ = ⊆: lemma
    where
    lemma : d₁ ×₂ r ⊆₂' d₂ ×₂ r
    lemma x y = map₁ (⊆₁-apply d₁⊆d₂)


module _ {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b}
    {Q : REL A B ℓ₁} {d : Pred A ℓ₂} {r₁ : Pred B ℓ₃} {r₂ : Pred B ℓ₄} where

  ×₂-⊆ʳ :
      r₁ ⊆₁ r₂
      ------------------
    → d ×₂ r₁ ⊆₂ d ×₂ r₂
  ×₂-⊆ʳ r₁⊆r₂ = ⊆: lemma
    where
    lemma : d ×₂ r₁ ⊆₂' d ×₂ r₂
    lemma x y = map₂ (⊆₁-apply r₁⊆r₂)


module _ {a b c ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b} {C : Set c}
    {d₁ : Pred A ℓ₁} {r₁ : Pred B ℓ₂} {d₂ : Pred B ℓ₃} {r₂ : Pred C ℓ₄} where

  ×₂-combine-⨾ : ( d₁ ×₂ r₁ ) ⨾ ( d₂ ×₂ r₂ ) ⊆₂ d₁ ×₂ r₂
  ×₂-combine-⨾ = ⊆: lemma
    where
    lemma : ( d₁ ×₂ r₁ ) ⨾ ( d₂ ×₂ r₂ ) ⊆₂' d₁ ×₂ r₂
    lemma x y ((d₁x , r₁z) ⨾[ z ]⨾ (d₂z , r₂y)) = (d₁x , r₂y)
