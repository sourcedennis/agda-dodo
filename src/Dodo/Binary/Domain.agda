{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Domain where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Function.Base using (flip; _∘_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel; REL)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Unary.Union
open import Dodo.Binary.Equality
open import Dodo.Binary.Composition


-- # Definitions

-- | The domain of the binary relation
dom : ∀ {a b ℓ : Level} {A : Set a} {B : Set b}
  → REL A B ℓ
    --------------
  → Pred A (b ⊔ ℓ)
dom R x = ∃[ y ] (R x y)

-- | The co-domain (or range) of the binary relation
--
--
-- # Design decision: Not range
--
-- It is somewhat arbitrary what constitutes the /co-domain/ of a binary relation,
-- and how it differs from its /range/. Usually, the /co-domain/ denotes the set of
-- /possible/ outputs of a function, while the /range/ denotes the set of /actual/
-- outputs. When considering functions, the /domain/ is a set of /independent/ variables,
-- while the /co-domain/ is the set variables that are /dependent/ on the domain.
--
-- However, when considering /relations/ (as opposed to mere functions), this dependency
-- is (usually) absent; Or could be inverted, where the domain "depends on" the codomain.
-- Under such interpretation, distinguishing co-domain from range is rather arbitrary.
codom : ∀ {a b ℓ : Level} {A : Set a} {B : Set b}
  → REL A B ℓ
    --------------
  → Pred B (a ⊔ ℓ)
codom R y = ∃[ x ] (R x y)

-- | The domain and co-domain of the binary relation
--
-- Conventionally named after: Union (of) Domain (and) Range
udr : ∀ {a ℓ : Level} {A : Set a}
  → Rel A ℓ
    --------------
  → Pred A (a ⊔ ℓ)
udr R = dom R ∪₁ codom R


-- # Operations

-- ## Operations: dom / codom / udr

-- | Weakens an element of a relation's domain to an element of its udr.
--
-- Note that Agda is unable to infer `R` from `x ∈ dom R`.
-- (As `R` may be beta-reduced inside the latter, I think)
dom⇒udr : ∀ {a ℓ : Level} {A : Set a} (R : Rel A ℓ) {x : A} → x ∈ dom R → x ∈ udr R
dom⇒udr _ = inj₁

-- | Weakens an element of a relation's co-domain to an element of its udr.
--
-- Note that Agda is unable to infer `R` from `x ∈ dom R`.
-- (As `R` may be beta-reduced inside the latter, I think)
codom⇒udr : ∀ {a ℓ : Level} {A : Set a} (R : Rel A ℓ) {x : A} → x ∈ codom R → x ∈ udr R
codom⇒udr _ = inj₂


module _ {a b ℓ : Level} {A : Set a} {B : Set b} where

  -- | Takes an inhabitant of `R x y` as proof that `x` is in the domain of `R`.
  --
  -- Note that `R` must be provided /explicitly/, as it may not always be inferred
  -- from its applied type.
  take-dom : (R : REL A B ℓ) → {x : A} {y : B} → R x y → x ∈ dom R
  take-dom R {x} {y} Rxy = (y , Rxy)

  -- | Takes an inhabitant of `R x y` as proof that `y` is in the co-domain of `R`.
  --
  -- Note that `R` must be provided /explicitly/, as it may not always be inferred
  -- from its applied type.
  take-codom : (R : REL A B ℓ) → {x : A} {y : B} → R x y → y ∈ codom R
  take-codom R {x} {y} Rxy = (x , Rxy)


module _ {a ℓ : Level} {A : Set a} where

  -- | Takes an inhabitant of `R x y` as proof that `x` is in the udr of `R`.
  --
  -- Note that `R` must be provided /explicitly/, as it may not always be inferred
  -- from its applied type.
  take-udrˡ : (R : Rel A ℓ) → {x y : A} → R x y → x ∈ udr R
  take-udrˡ R Rxy = dom⇒udr R (take-dom R Rxy)

  -- | Takes an inhabitant of `R x y` as proof that `y` is in the udr of `R`.
  --
  -- Note that `R` must be provided /explicitly/, as it may not always be inferred
  -- from its applied type.
  take-udrʳ : (R : Rel A ℓ) → {x y : A} → R x y → y ∈ udr R
  take-udrʳ R Rxy = codom⇒udr R (take-codom R Rxy)
  

module _ {a b ℓ₁ ℓ₂ : Level} {A : Set a} {B : Set b}
    {P : REL A B ℓ₁} {Q : REL A B ℓ₂} where

  dom-preserves-⊆ : P ⊆₂ Q → dom P ⊆₁ dom Q
  dom-preserves-⊆ P⊆Q = ⊆: λ{x (y , Pxy) → (y , un-⊆₂ P⊆Q x y Pxy)}

  codom-preserves-⊆ : P ⊆₂ Q → codom P ⊆₁ codom Q
  codom-preserves-⊆ P⊆Q = ⊆: λ{y (x , Pxy) → (x , un-⊆₂ P⊆Q x y Pxy)}


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {P : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  udr-preserves-⊆ : P ⊆₂ Q → udr P ⊆₁ udr Q
  udr-preserves-⊆ P⊆Q = ⊆: lemma
    where
    lemma : udr P ⊆₁' udr Q
    lemma x (inj₁ x∈dom)   = dom⇒udr Q (⊆₁-apply (dom-preserves-⊆ P⊆Q) x∈dom)
    lemma y (inj₂ y∈codom) = codom⇒udr Q (⊆₁-apply (codom-preserves-⊆ P⊆Q) y∈codom)


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a}
    {P : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  udr-combine-⨾ : udr (P ⨾ Q) ⊆₁ udr P ∪₁ udr Q
  udr-combine-⨾ = ⊆: lemma
    where
    lemma : udr (P ⨾ Q) ⊆₁' (udr P ∪₁ udr Q)
    lemma _ (inj₁ (a , (Pxb ⨾[ b ]⨾ Qba))) = inj₁ (inj₁ (b , Pxb))
    lemma _ (inj₂ (a , (Pab ⨾[ b ]⨾ Qbx))) = inj₂ (inj₂ (b , Qbx))


module _ {a ℓ : Level} {A : Set a}
    {P : Rel A ℓ} where

  udr-flip : udr P ⇔₁ udr (flip P)
  udr-flip = ⇔: (λ _ → swap) (λ _ → swap)

  dom-flip : dom P ⇔₁ codom (flip P)
  dom-flip = ⇔: (λ _ z → z) (λ _ z → z)

  codom-flip : codom P ⇔₁ dom (flip P)
  codom-flip = ⇔: (λ _ z → z) (λ _ z → z)
