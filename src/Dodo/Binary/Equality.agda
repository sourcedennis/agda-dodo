{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Equality where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Symmetric)
-- Local imports
open import Dodo.Unary.Equality


private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C D : Set a


-- same precedence as _≡_
infix 4 _⊆₂'_ _⊆₂_ _⇔₂_ _⊇₂_

-- | Binary relation subset helper. Generally, use `_⊆₂_` (below).
--
--
-- # Design decision: Explicit variables
-- 
-- `x` and `y` are passed /explicitly/. If they were implicit, Agda tries (and often fails) to
-- instantiate them at inappropriate applications.
_⊆₂'_ : REL (REL A B ℓ₁) (REL A B ℓ₂) _
_⊆₂'_ {A = A} {B = B} P R = ∀ (x : A) (y : B) → P x y → R x y


-- | Binary relation subset
--
-- Note that this does /not/ describe structural equality between inhabitants, only
-- "(directed) co-inhabitation".
-- `P ⊆₂ Q` denotes: If `P x y` is inhabited, then `Q x y` is inhabited.
--
-- Whatever these inhabitants are, is irrelevant w.r.t. the subset constraint.
--
--
-- # Design decision: Include P and R in the type
--
-- Somehow, Agda cannot infer P and R from `P ⇒ R`, and requires them explicitly passed.
-- For proof convenience, wrap the proof in this structure, which explicitly conveys P and R
-- to the type-checker.
data _⊆₂_ {A : Set a} {B : Set b} (P : REL A B ℓ₁) (R : REL A B ℓ₂) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  ⊆: : P ⊆₂' R → P ⊆₂ R


-- | Binary relation equality
--
-- Note that this does /not/ describe structural equality between inhabitants, only
-- "co-inhabitation".
-- `P ⇔₂ Q` denotes: `P x y` is inhabited iff `Q x y` is inhabited.
--
-- Whatever these inhabitants are, is irrelevant w.r.t. the equality constraint.
--
--
-- # Design decision: Include P and R in the type
--
-- Somehow, Agda cannot infer P and R from `P ⇔ R`, and requires them explicitly passed.
-- For proof convenience, wrap the proof in this structure, which explicitly conveys P and R
-- to the type-checker.
data _⇔₂_ {A : Set a} {B : Set b} (P : REL A B ℓ₁) (R : REL A B ℓ₂) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  ⇔: : P ⊆₂' R → R ⊆₂' P → P ⇔₂ R


-- | Binary relation superset
_⊇₂_ : REL (REL A B ℓ₁) (REL A B ℓ₂) _
P ⊇₂ R = R ⊆₂ P


-- # Helpers

-- | Unwraps the `⊆:` constructor
un-⊆₂ : {P : REL A B ℓ₁} {R : REL A B ℓ₂}
  → P ⊆₂ R
    -------
  → P ⊆₂' R
un-⊆₂ (⊆: P⊆R) = P⊆R

-- | Unlifts a function over `⊆₂` to its unwrapped variant over `⊆₂'`.
unlift-⊆₂ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL C D ℓ₃} {S : REL C D ℓ₄}
  → ( P ⊆₂ Q → R ⊆₂ S )
    ---------------------
  → ( P ⊆₂' Q → R ⊆₂' S )
unlift-⊆₂ f P⊆Q = un-⊆₂ (f (⊆: P⊆Q))

-- | Lifts a function over `⊆₂'` to its wrapped variant over `⊆₂`.
lift-⊆₂ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL C D ℓ₃} {S : REL C D ℓ₄}
  → ( P ⊆₂' Q → R ⊆₂' S )
    ---------------------
  → ( P ⊆₂ Q → R ⊆₂ S )
lift-⊆₂ f (⊆: P⊆Q) = ⊆: (f P⊆Q)

-- | Introduces an equality `⇔₂` from both bi-directional components.
⇔₂-intro :
    {P : REL A B ℓ₁} {R : REL A B ℓ₂}
  → P ⊆₂ R
  → R ⊆₂ P
    ------
  → P ⇔₂ R
⇔₂-intro (⊆: P⊆R) (⊆: R⊆P) = ⇔: P⊆R R⊆P

-- | Construct an equality `⇔₂` from a mapping over both bi-directional components.
⇔₂-compose :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL C D ℓ₃} {S : REL C D ℓ₄}
  → ( P ⊆₂ Q → R ⊆₂ S )
  → ( Q ⊆₂ P → S ⊆₂ R )
  → P ⇔₂ Q
    -------------------
  → R ⇔₂ S
⇔₂-compose ⊆-proof ⊇-proof (⇔: P⊆Q R⊆S) = ⇔₂-intro (⊆-proof (⊆: P⊆Q)) (⊇-proof (⊆: R⊆S))

-- | Construct a /binary/ equality `⇔₂` from a mapping over both bi-directional components of a /unary/ relation.
⇔₂-compose-⇔₁ :
    {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : REL B C ℓ₃} {S : REL B C ℓ₄}
  → ( P ⊆₁ Q → R ⊆₂ S )
  → ( Q ⊆₁ P → S ⊆₂ R )
  → P ⇔₁ Q
    -------------------
  → R ⇔₂ S
⇔₂-compose-⇔₁ ⊆-proof ⊇-proof (⇔: P⊆Q R⊆S) = ⇔₂-intro (⊆-proof (⊆: P⊆Q)) (⊇-proof (⊆: R⊆S))

-- | Construct a /unary/ equalty `⇔₁` from a mapping over both bi-directional components of a /binary/ relation.
⇔₁-compose-⇔₂ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : Pred C ℓ₃} {S : Pred C ℓ₄}
  → ( P ⊆₂ Q → R ⊆₁ S )
  → ( Q ⊆₂ P → S ⊆₁ R )
  → P ⇔₂ Q
    -------------------
  → R ⇔₁ S
⇔₁-compose-⇔₂ ⊆-proof ⊇-proof (⇔: P⊆Q R⊆S) = ⇔₁-intro (⊆-proof (⊆: P⊆Q)) (⊇-proof (⊆: R⊆S))


-- # Properties

-- ## Properties: ⊆₂

module _ {R : REL A B ℓ₁} where

  ⊆₂-refl : R ⊆₂ R
  ⊆₂-refl = ⊆: (λ _ _ Rxy → Rxy)

module _ {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL A B ℓ₃} where
    
  ⊆₂-trans : P ⊆₂ Q → Q ⊆₂ R → P ⊆₂ R
  ⊆₂-trans (⊆: P⊆Q) (⊆: Q⊆R) = ⊆: (λ x y Pxy → Q⊆R x y (P⊆Q x y Pxy))


-- ## Properties: ⇔₂

module _ {R : REL A B ℓ₁} where

  ⇔₂-refl : R ⇔₂ R
  ⇔₂-refl = ⇔₂-intro ⊆₂-refl ⊆₂-refl

module _ {Q : REL A B ℓ₁} {R : REL A B ℓ₂} where

  -- | Symmetry of the `_⇔₂_` operation.
  --
  -- 
  -- # Design decision: No Symmetric
  --
  -- Do /not/ use `Symmetric _⇔₂_` as its type. It messes up the universe levels.
  ⇔₂-sym : Q ⇔₂ R → R ⇔₂ Q
  ⇔₂-sym (⇔: Q⊆R R⊆Q) = ⇔: R⊆Q Q⊆R

module _ {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL A B ℓ₃} where

  ⇔₂-trans : P ⇔₂ Q → Q ⇔₂ R → P ⇔₂ R
  ⇔₂-trans (⇔: P⊆Q Q⊆P) (⇔: Q⊆R R⊆Q) =
    ⇔₂-intro (⊆₂-trans (⊆: P⊆Q) (⊆: Q⊆R)) (⊆₂-trans (⊆: R⊆Q) (⊆: Q⊆P))


-- # Operations

-- ## Operations: ⇔₂ and ⊆₂ conversion

⇔₂-to-⊆₂ : {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
  → P ⇔₂ Q
    ------
  → P ⊆₂ Q
⇔₂-to-⊆₂ (⇔: P⊆Q _) = ⊆: P⊆Q

⇔₂-to-⊇₂ : {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
  → P ⇔₂ Q
    ------
  → Q ⊆₂ P
⇔₂-to-⊇₂ (⇔: _ Q⊆P) = ⊆: Q⊆P


-- ## Operations: ⊆₂

⊆₂-apply :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
  → P ⊆₂ Q
  → {x : A} {y : B}
  → P x y
    ---------------
  → Q x y
⊆₂-apply (⊆: P⊆Q) {x} {y} = P⊆Q x y

-- | Substitute an equal relation (under `⇔₂`) for the left-hand side of a subset definition.
⊆₂-substˡ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL A B ℓ₃}
  → P ⇔₂ Q
  → P ⊆₂ R
    ------
  → Q ⊆₂ R
⊆₂-substˡ (⇔: _ Q⊆P) P⊆R = ⊆₂-trans (⊆: Q⊆P) P⊆R

-- | Substitute an equal relation (under `⇔₂`) for the right-hand side of a subset definition.
⊆₂-substʳ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL A B ℓ₃}
  → Q ⇔₂ R
  → P ⊆₂ Q
    ------
  → P ⊆₂ R
⊆₂-substʳ (⇔: Q⊆R _) P⊆Q = ⊆₂-trans P⊆Q (⊆: Q⊆R)

-- | Weaken intentional equality of relations to their subset `⊆₂` definition.
≡-to-⊆₂ :
    {P Q : REL A B ℓ₁}
  → P ≡ Q
    ------
  → P ⊆₂ Q
≡-to-⊆₂ refl = ⊆: (λ _ _ Pxy → Pxy)

-- | Weaken intentional equality of relations to their superset definition (inverted `⊆₂`).
≡-to-⊇₂ :
    {P Q : REL A B ℓ₁}
  → P ≡ Q
    ------
  → Q ⊆₂ P
≡-to-⊇₂ refl = ⊆: (λ _ _ Qxy → Qxy)

-- | Substitute both elements of the relation's instantiation.
subst-rel :
    (R : REL A B ℓ₁)
  → {x₁ x₂ : A}
  → x₁ ≡ x₂
  → {y₁ y₂ : B}
  → y₁ ≡ y₂
  → R x₁ y₁
    -----------------------
  → R x₂ y₂
subst-rel _ refl refl Rxy = Rxy


-- ## Operations: ⇔₂

⇔₂-apply-⊆₂ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
  → P ⇔₂ Q
  → {x : A} {y : B}
  → P x y
    ---------------
  → Q x y
⇔₂-apply-⊆₂ = ⊆₂-apply ∘ ⇔₂-to-⊆₂

⇔₂-apply-⊇₂ :
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
  → P ⇔₂ Q
  → {x : A} {y : B}
  → Q x y
    ---------------
  → P x y
⇔₂-apply-⊇₂ = ⊆₂-apply ∘ ⇔₂-to-⊇₂

≡-to-⇔₂ :
    {P Q : REL A B ℓ₁}
  → P ≡ Q
    ------
  → P ⇔₂ Q
≡-to-⇔₂ refl = ⇔₂-intro ⊆₂-refl ⊆₂-refl


-- # Reasoning

-- ## Reasoning: ⊆₂

-- | A collection of functions for writing subset proofs over binary relations.
--
-- 
-- # Example
--
-- ```
-- proof P Q R S =
--   begin⊆₂
--     (P ⨾ Q) ⨾ (R ⨾ S)
--   ⊆₂⟨ ⇔₂-to-⊇₂ ⨾-assoc ⟩
--     ((P ⨾ Q) ⨾ R) ⨾ S
--   ⊆₂⟨ ⨾-substˡ-⊆₂ (⇔₂-to-⊆₂ ⨾-assoc) ⟩
--     P ⨾ (Q ⨾ R) ⨾ S
--   ⊆₂∎
-- ```
module ⊆₂-Reasoning where

  infix  3 _⊆₂∎
  infixr 2 step-⊆₂
  infix  1 begin⊆₂_

  begin⊆₂_ : {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
    → P ⊆₂ Q
    → P ⊆₂ Q
  begin⊆₂_ P⊆Q = P⊆Q

  step-⊆₂ :
      (P : REL A B ℓ₁)
    → {Q : REL A B ℓ₂}
    → {R : REL A B ℓ₃}
    → Q ⊆₂ R
    → P ⊆₂ Q
    → P ⊆₂ R
  step-⊆₂ P Q⊆R P⊆Q = ⊆₂-trans P⊆Q Q⊆R

  _⊆₂∎ : ∀ (P : REL A B ℓ₁) → P ⊆₂ P
  _⊆₂∎ P = ⊆: (λ _ _ z → z)

  syntax step-⊆₂ P Q⊆R P⊆Q = P ⊆₂⟨ P⊆Q ⟩ Q⊆R


-- ## Reasoning: ⇔₂

-- | A collection of functions for writing equality proofs over binary relations.
--
--
-- # Example
--
-- ```
-- proof P Q R S =
--   begin⇔₂
--     (P ⨾ Q) ⨾ (R ⨾ S)
--   ⇔₂⟨ ⇔₂-sym ⨾-assoc ⟩
--     ((P ⨾ Q) ⨾ R) ⨾ S
--   ⇔₂⟨ ⨾-substˡ ⨾-assoc ⟩
--     P ⨾ (Q ⨾ R) ⨾ S
--   ⇔₂∎
-- ```
module ⇔₂-Reasoning where

  infix  3 _⇔₂∎
  infixr 2 _⇔₂⟨⟩_ step-⇔₂
  infix  1 begin⇔₂_

  begin⇔₂_ : {P : REL A B ℓ₁} {Q : REL A B ℓ₂}
    → P ⇔₂ Q
    → P ⇔₂ Q
  begin⇔₂_ P⇔Q = P⇔Q

  _⇔₂⟨⟩_ :
      (P : REL A B ℓ₁)
    → {Q : REL A B ℓ₂}
    → P ⇔₂ Q
    → P ⇔₂ Q
  _ ⇔₂⟨⟩ x≡y = x≡y

  step-⇔₂ :
      (P : REL A B ℓ₁)
    → {Q : REL A B ℓ₂}
    → {R : REL A B ℓ₃}
    → Q ⇔₂ R
    → P ⇔₂ Q
    → P ⇔₂ R
  step-⇔₂ _ Q⇔R P⇔Q = ⇔₂-trans P⇔Q Q⇔R

  _⇔₂∎ : ∀ (P : REL A B ℓ₁) → P ⇔₂ P
  _⇔₂∎ _ = ⇔₂-refl

  syntax step-⇔₂ P Q⇔R P⇔Q = P ⇔₂⟨ P⇔Q ⟩ Q⇔R
