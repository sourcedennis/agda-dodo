{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Filter where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong; cong₂) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level; _⊔_)
open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Transitive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Unary.Unique
open import Dodo.Binary.Equality
open import Dodo.Binary.Transitive


private
  variable
    a ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a


-- # Definitions

-- | A value of type `A` with a proof that it satisfies the given predicate `P`.
--
--
-- # Design Decision: Alternative to `P x`
--
-- One might argue that a function could just as well take:
-- > f : {x : A} → P x → ...
--
-- In that case, the `with-pred` constructor adds nothing. However, crucially,
-- the inhabitant of `A` is /not/ included in the type signature of `WithPred`.
-- This means, a relation may be defined over elements of type `WithPred`.
-- While a relation /cannot/ be defined over elements of type `P x`, because
-- `x` varies.
data WithPred {A : Set a} (P : Pred A ℓ) : Set (a ⊔ ℓ) where
  with-pred : (x : A) → P x → WithPred P

-- | Helper for extracting element equality from an instance of `WithPred`.
--
-- This is tricky to unify otherwise in larger contexts, as `Px` and `Py` have
-- different /types/ when `x` and `y` are unequal.
with-pred-≡ : {P : Pred A ℓ} {x y : A} {Px : P x} {Py : P y}
  → with-pred x Px ≡ with-pred y Py
    -------------------------------
  → x ≡ y
with-pred-≡ refl = refl

-- | Instances of `WithPred` are equal if they are defined over the same value,
-- and its predicate is unique.
with-pred-unique : {P : Pred A ℓ}
  → UniquePred P
  → {x y : A}
  → x ≡ y
  → (Px : P x) (Py : P y)
    -------------------------------
  → with-pred x Px ≡ with-pred y Py
with-pred-unique uniqueP {x} refl Px Py = cong (with-pred x) (uniqueP _ Px Py)


with-pred-≢ : {P : Pred A ℓ}
  → UniquePred P
  → {x y : A} {Px : P x} {Py : P y}
  → with-pred x Px ≢ with-pred y Py
    -------------------------------
  → x ≢ y
with-pred-≢ uniqueP Px≢Py x≡y = Px≢Py (with-pred-unique uniqueP x≡y _ _)


-- | A relation whose elements all satisfy `P`.
--
-- Note that this differs from defining:
-- > R ∩₂ ( P ×₂ P )
--
-- In that case, the type signature is still identical to the type signature of
-- `R` (except for the universe level). However, `filter-rel` alters the type,
-- which proves no other inhabitants can exist.
--
-- This is in particular useful for properties that are declared over an entire
-- relation (such as `Trichotomous`), while they should only hold over a subset
-- of it.
--
-- 
-- # Example
--
-- For instance, consider:
-- (1) > Trichotomous _≡_ (filter-rel P R)
-- and
-- (2) > Trichotomous _≡_ (R ∩₂ ( P ×₂ P ))
--
-- Where the corresponding types are:
-- > R : Rel A ℓzero
-- > P : Pred A ℓzero
--
-- The type of the relation in (1) is then:
-- > filter-rel P R : Rel (WithPred P) ℓzero
-- While the type of the relation in (2) is:
-- > (R ∩₂ (P ×₂ P)) : Rel A ℓzero
--
-- So, for (2), defining `Trichotomous` means that it finds an instance of
-- `P` for both elements, even when no such `P x` exists; Which leads to a
-- contradiction. Whereas (1) will only find the relation if `P` holds for both
-- elements.
--
-- Effectively, (2) implies:
-- > ∀ (x : A) → P x
--
-- Whereas (1) makes no such strong claims.
filter-rel :
    (P : Pred A ℓ₁)
  → Rel A ℓ₂
    -------------------
  → Rel (WithPred P) ℓ₂
filter-rel P R (with-pred x Px) (with-pred y Py) = R x y

-- | Effectively the inverse of `filter-rel`.
--
-- It loses the type-level restrictions, but preserves the restrictions on
-- value-level.
unfilter-rel :
    {P : Pred A ℓ₁}
  → Rel (WithPred P) ℓ₂
    -------------------
  → Rel A (ℓ₁ ⊔ ℓ₂)
unfilter-rel R x y = ∃[ Px ] ∃[ Py ] R (with-pred x Px) (with-pred y Py)

-- | Helper for unwrapping the value from the `with-pred` constructor.
un-with-pred : {P : Pred A ℓ}
  → WithPred P
    ----------
  → A
un-with-pred (with-pred x _) = x

⁺-strip-filter :
    {P : Pred A ℓ₁}
  → {R : Rel A ℓ₂}
  → {x y : A}
  → {Px : P x} {Py : P y}
  → TransClosure (filter-rel P R) (with-pred x Px) (with-pred y Py)
    ---------------------------------------------------------------
  → TransClosure R x y
⁺-strip-filter [ x∼y ] = [ x∼y ]
⁺-strip-filter (_∷_ {_} {with-pred z Pz} Rxz R⁺zy) = Rxz ∷ ⁺-strip-filter R⁺zy

-- | Apply a relation filter to a chain /from right to left/.
--
-- This applies when a predicate `P x` is true whenever `R x y` and `P y` are true.
-- Then, for any chain where `P` holds for the final element, it holds for every
-- element in the chain.
⁺-filter-relˡ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → P y → R x y → P x)
  → {x y : A}
  → (Px : P x) (Py : P y)
  → (R⁺xy : TransClosure R x y)
    ---------------------------------------------------------------
  → TransClosure (filter-rel P R) (with-pred x Px) (with-pred y Py)
⁺-filter-relˡ f Px Py [ Rxy ]        = [ Rxy ]
⁺-filter-relˡ f Px Py ( Rxz ∷ R⁺zy ) = Rxz ∷ ⁺-filter-relˡ f (⁺-predˡ f R⁺zy Py) Py R⁺zy

-- | Apply a relation filter to a chain /from left to right/.
--
-- This applies when a predicate `P y` is true whenever `R x y` and `P x` are true.
-- Then, for any chain where `P` holds for the first element, it holds for every
-- element in the chain.
⁺-filter-relʳ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → P x → R x y → P y)
  → {x y : A}
  → (Px : P x) (Py : P y)
  → (R⁺xy : TransClosure R x y)
    ---------------------------------------------------------------
  → TransClosure (filter-rel P R) (with-pred x Px) (with-pred y Py)
⁺-filter-relʳ f Px Py [ Rxy ]        = [ Rxy ]
⁺-filter-relʳ f Px Py ( Rxz ∷ R⁺zy ) = Rxz ∷ ⁺-filter-relʳ f (f Px Rxz) Py R⁺zy


-- # Properties

with-pred-⊆₁ : {P : Pred A ℓ₁} {Q : Pred A ℓ₂}
  → P ⊆₁ Q
  → WithPred P
    ----------
  → WithPred Q
with-pred-⊆₁ P⊆Q (with-pred x Px) = with-pred x (⊆₁-apply P⊆Q Px)

filter-rel-⊆₂ :
    (R : Rel A ℓ₁)
  → {P : Pred A ℓ₂}
    ----------------------------------
  → unfilter-rel (filter-rel P R) ⊆₂ R
filter-rel-⊆₂ R {P} = ⊆: ⊆-proof
  where
  ⊆-proof : unfilter-rel (filter-rel P R) ⊆₂' R
  ⊆-proof _ _ (_ , _ , Rxy) = Rxy


module _ {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Rel A ℓ₃} where

  filter-rel-preserves-⊆₁ :
      P ⊆₁ Q
      --------------------------------------------------------------
    → unfilter-rel (filter-rel P R) ⊆₂ unfilter-rel (filter-rel Q R)
  filter-rel-preserves-⊆₁ P₁⊆P₂ = ⊆: lemma
    where
    lemma : unfilter-rel (filter-rel P R) ⊆₂' unfilter-rel (filter-rel Q R)
    lemma _ _ (P₁x , P₁y , Qxy) = (⊆₁-apply P₁⊆P₂ P₁x , ⊆₁-apply P₁⊆P₂ P₁y , Qxy)

  -- |
  --
  -- Note that this does /not/ hold in general for subsets of relations.
  -- That is, the following does /not/ hold:
  -- > Q ⊆₂ R → Transitive R → Transitive Q
  --
  -- After all, if `Q x y` and `Q y z` hold, then `R x y` and `R y z` hold,
  -- then `R x z` holds. However, it does not mean that `Q x z` holds.
  trans-filter-rel-⊆₁ :
      P ⊆₁ Q
    → Transitive (filter-rel Q R)
      ---------------------------
    → Transitive (filter-rel P R)
  trans-filter-rel-⊆₁ P⊆Q transQR {Pi} {Pj} {Pk} Rij Rjk =
    let Qi = with-pred-⊆₁ P⊆Q Pi
        Qj = with-pred-⊆₁ P⊆Q Pj
        Qk = with-pred-⊆₁ P⊆Q Pk
    in Q⇒P {Pi} {Pk} (transQR {Qi} {Qj} {Qk} (P⇒Q {Pi} {Pj} Rij) (P⇒Q {Pj} {Pk} Rjk))
    where
    P⇒Q : ∀ {x y : WithPred P} → filter-rel P R x y → filter-rel Q R (with-pred-⊆₁ P⊆Q x) (with-pred-⊆₁ P⊆Q y)
    P⇒Q {with-pred _ _} {with-pred _ _} Rxy = Rxy
    
    Q⇒P : ∀ {x y : WithPred P} → filter-rel Q R (with-pred-⊆₁ P⊆Q x) (with-pred-⊆₁ P⊆Q y) → filter-rel P R x y
    Q⇒P {with-pred _ _} {with-pred _ _} Rxy = Rxy


module _ {P : Pred A ℓ₁} {R : Rel A ℓ₂} {Q : Rel A ℓ₃} where

  filter-rel-preserved-⊆₂ :
      R ⊆₂ Q
      --------------------------------------------------------------
    → unfilter-rel (filter-rel P R) ⊆₂ unfilter-rel (filter-rel P Q)
  filter-rel-preserved-⊆₂ R⊆Q = ⊆: lemma
    where
    lemma : unfilter-rel (filter-rel P R) ⊆₂' unfilter-rel (filter-rel P Q)
    lemma x y (Px , Py , Rxy) = Px , Py , ⊆₂-apply R⊆Q Rxy


-- # Operations

module _ {R : Rel A ℓ₁} {P : Pred A ℓ₂} where

  filter-rel-dom : {x y : A}
    → unfilter-rel (filter-rel P R) x y
      ---------------------------------
    → x ∈ P
  filter-rel-dom (Px , Py , Rxy) = Px
  
  filter-rel-codom : {x y : A}
    → unfilter-rel (filter-rel P R) x y
      ---------------------------------
    → y ∈ P
  filter-rel-codom (Px , Py , Rxy) = Py
