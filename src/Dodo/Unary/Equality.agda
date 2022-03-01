{-# OPTIONS --without-K --safe #-}

module Dodo.Unary.Equality where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Relation.Unary using (Pred)


-- # Definitions

infix 4 _⊆₁'_ _⊆₁_ _⇔₁_

-- Binary relation subset helper. Generally, use `_⊆₁_` (below).
_⊆₁'_ : {a ℓ₁ ℓ₂ : Level} {A : Set a}
  → (P : Pred A ℓ₁)
  → (R : Pred A ℓ₂)
  → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
_⊆₁'_ {A = A} P R = ∀ (x : A) → P x → R x

-- Somehow, Agda cannot infer P and R from `P ⇒ R`, and requires them explicitly passed.
-- For proof convenience, wrap the proof in this structure, which explicitly conveys P and R
-- to the type-checker.
data _⊆₁_ {a ℓ₁ ℓ₂ : Level} {A : Set a} (P : Pred A ℓ₁) (R : Pred A ℓ₂) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  ⊆: : P ⊆₁' R → P ⊆₁ R

data _⇔₁_ {a ℓ₁ ℓ₂ : Level} {A : Set a} (P : Pred A ℓ₁) (R : Pred A ℓ₂) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  ⇔: : P ⊆₁' R → R ⊆₁' P → P ⇔₁ R


-- # Helpers

⇔₁-intro : {a ℓ₁ ℓ₂ : Level} {A : Set a}
  → {P : Pred A ℓ₁} {R : Pred A ℓ₂}
  → P ⊆₁ R
  → R ⊆₁ P
  → P ⇔₁ R
⇔₁-intro (⊆: P⊆R) (⊆: R⊆P) = ⇔: P⊆R R⊆P

⇔₁-compose : ∀ {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred B ℓ₃} {S : Pred B ℓ₄}
  → ( P ⊆₁ Q → R ⊆₁ S )
  → ( Q ⊆₁ P → S ⊆₁ R )
  → P ⇔₁ Q
  → R ⇔₁ S
⇔₁-compose ⊆-proof ⊇-proof (⇔: P⊆Q R⊆S) = ⇔₁-intro (⊆-proof (⊆: P⊆Q)) (⊇-proof (⊆: R⊆S))


-- # Properties

-- ## Properties: ⊆₁

module _ {a ℓ : Level} {A : Set a} {R : Pred A ℓ} where

  ⊆₁-refl : R ⊆₁ R
  ⊆₁-refl = ⊆: (λ _ Rx → Rx)

module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ⊆₁-trans : P ⊆₁ Q → Q ⊆₁ R → P ⊆₁ R
  ⊆₁-trans (⊆: P⊆Q) (⊆: Q⊆R) = ⊆: (λ x Qx → Q⊆R x (P⊆Q x Qx))
  

-- ## Properties: ⇔₁

module _ {a ℓ : Level} {A : Set a} {R : Pred A ℓ} where

  ⇔₁-refl : R ⇔₁ R
  ⇔₁-refl = ⇔₁-intro ⊆₁-refl ⊆₁-refl

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {Q : Pred A ℓ₁} {R : Pred A ℓ₂} where

  ⇔₁-sym : Q ⇔₁ R → R ⇔₁ Q
  -- WARNING: Do *NOT* use `Symmetric _⇔_`. It messes up the universe levels.
  ⇔₁-sym (⇔: Q⊆R R⊆Q) = ⇔: R⊆Q Q⊆R

module _ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} where

  ⇔₁-trans : P ⇔₁ Q → Q ⇔₁ R → P ⇔₁ R
  ⇔₁-trans (⇔: P⊆Q Q⊆P) (⇔: Q⊆R R⊆Q) = ⇔₁-intro (⊆₁-trans (⊆: P⊆Q) (⊆: Q⊆R)) (⊆₁-trans (⊆: R⊆Q) (⊆: Q⊆P))


-- # Operations

-- ## Operations: ⇔₁ and ⊆₁ conversion

un-⊆₁ : ∀ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {R : Pred A ℓ₂}
  → P ⊆₁ R
  → P ⊆₁' R
un-⊆₁ (⊆: P⊆R) = P⊆R

unlift-⊆₁ : ∀ {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred B ℓ₃} {S : Pred B ℓ₄}
  → ( P ⊆₁ Q → R ⊆₁ S )
  → ( P ⊆₁' Q → R ⊆₁' S )
unlift-⊆₁ f P⊆Q = un-⊆₁ (f (⊆: P⊆Q))

lift-⊆₁ : ∀ {a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred B ℓ₃} {S : Pred B ℓ₄}
  → ( P ⊆₁' Q → R ⊆₁' S )
  → ( P ⊆₁ Q → R ⊆₁ S )
lift-⊆₁ f (⊆: P⊆Q) = ⊆: (f P⊆Q)

⇔₁-to-⊆₁ : {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
  → P ⇔₁ Q
    ------
  → P ⊆₁ Q
⇔₁-to-⊆₁ (⇔: P⊆Q _) = ⊆: P⊆Q

⇔₁-to-⊇₁ : {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
  → P ⇔₁ Q
    ------
  → Q ⊆₁ P
⇔₁-to-⊇₁ (⇔: _ Q⊆P) = ⊆: Q⊆P


-- ## Operations: ⊆₁

⊆₁-apply : ∀ {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
  → P ⊆₁ Q
  → {x : A}
  → P x
    -------
  → Q x
⊆₁-apply (⊆: P⊆Q) {x} = P⊆Q x

⊆₁-substˡ : ∀ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃} {x : A}
  → P ⇔₁ Q
  → P ⊆₁ R
    ------
  → Q ⊆₁ R
⊆₁-substˡ (⇔: _ Q⊆P) P⊆R = ⊆₁-trans (⊆: Q⊆P) P⊆R

⊆₁-substʳ : ∀ {a ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃}
  → Q ⇔₁ R
  → P ⊆₁ Q
    ------
  → P ⊆₁ R
⊆₁-substʳ (⇔: Q⊆R _) P⊆Q = ⊆₁-trans P⊆Q (⊆: Q⊆R)

≡-to-⊆₁ : {a b ℓ : Level} {A : Set a}
    {P : Pred A ℓ} {Q : Pred A ℓ}
  → P ≡ Q
    ------
  → P ⊆₁ Q
≡-to-⊆₁ refl = ⊆: (λ _ Px → Px)


-- ## Operations: ⇔₁

⇔₁-apply-⊆₁ : {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
  → P ⇔₁ Q
  → {x : A}
  → P x
    -------
  → Q x
⇔₁-apply-⊆₁ = ⊆₁-apply ∘ ⇔₁-to-⊆₁

⇔₁-apply-⊇₁ : {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
  → P ⇔₁ Q
  → {x : A}
  → Q x
    -------
  → P x
⇔₁-apply-⊇₁ = ⊆₁-apply ∘ ⇔₁-to-⊇₁

≡-to-⇔₁ : {a ℓ : Level} {A : Set a}
    {P : Pred A ℓ} {Q : Pred A ℓ}
  → P ≡ Q
    ------
  → P ⇔₁ Q
≡-to-⇔₁ refl = ⇔₁-intro ⊆₁-refl ⊆₁-refl


-- # Reasoning

-- ## Reasoning: ⊆₁

module ⊆₁-Reasoning {a ℓ₁ : Level} {A : Set a} where

  infix  3 _⊆₁∎
  infixr 2 step-⊆₁
  infix  1 begin⊆₁_

  begin⊆₁_ : {ℓ₂ : Level} {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
    → P ⊆₁ Q
      ------
    → P ⊆₁ Q
  begin⊆₁_ P⊆Q = P⊆Q

  step-⊆₁ : ∀ {ℓ₂ ℓ₃ : Level}
    → (P : Pred A ℓ₁)
    → {Q : Pred A ℓ₂}
    → {R : Pred A ℓ₃}
    → Q ⊆₁ R
    → P ⊆₁ Q
      ------
    → P ⊆₁ R
  step-⊆₁ P Q⊆R P⊆Q = ⊆₁-trans P⊆Q Q⊆R

  _⊆₁∎ : ∀ (P : Pred A ℓ₁) → P ⊆₁ P
  _⊆₁∎ _ = ⊆₁-refl

  syntax step-⊆₁ P Q⊆R P⊆Q = P ⊆₁⟨ P⊆Q ⟩ Q⊆R


-- ## Reasoning: ⇔₁

module ⇔₁-Reasoning {a ℓ₁ : Level} {A : Set a} where

  infix  3 _⇔₁∎
  infixr 2 _⇔₁⟨⟩_ step-⇔₁
  infix  1 begin⇔₁_

  begin⇔₁_ : {ℓ₂ : Level} {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
    → P ⇔₁ Q
      ------
    → P ⇔₁ Q
  begin⇔₁_ P⇔Q = P⇔Q

  _⇔₁⟨⟩_ : {ℓ₂ : Level}
      (P : Pred A ℓ₁)
    → {Q : Pred A ℓ₂}
    → P ⇔₁ Q
      ---------------
    → P ⇔₁ Q
  _ ⇔₁⟨⟩ x≡y = x≡y

  step-⇔₁ : ∀ {ℓ₂ ℓ₃ : Level}
    → (P : Pred A ℓ₁)
    → {Q : Pred A ℓ₂}
    → {R : Pred A ℓ₃}
    → Q ⇔₁ R
    → P ⇔₁ Q
      ---------------
    → P ⇔₁ R
  step-⇔₁ _ Q⇔R P⇔Q = ⇔₁-trans P⇔Q Q⇔R

  _⇔₁∎ : ∀ (P : Pred A ℓ₁) → P ⇔₁ P
  _⇔₁∎ _ = ⇔₁-refl

  syntax step-⇔₁ P Q⇔R P⇔Q = P ⇔₁⟨ P⇔Q ⟩ Q⇔R
