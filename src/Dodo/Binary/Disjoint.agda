{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Disjoint where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (suc to ℓsuc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL)
open import Data.List using (List; _∷_; []; all; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary using (¬_)
-- Local imports
open import Dodo.Binary.Empty
open import Dodo.Binary.Equality
open import Dodo.Binary.Intersection


-- # Definitions

-- | Predicate stating two binary relations are never inhabited for the same elements.
Disjoint₂ : ∀ {a b ℓ₁ ℓ₂ : Level} {A : Set a} {B : Set b}
  → REL A B ℓ₁ → REL A B ℓ₂ → Set _
Disjoint₂ P Q = Empty₂ (P ∩₂ Q)

-- | Given a predicate `P`, `Any₂ P xs` states that /at least two/ elements in
-- `xs` satisfy `P`.
data Any₂ {a ℓ : Level} {A : Set a} (P : Pred A ℓ) : Pred (List A) (a ⊔ ℓ) where
  here  : ∀ {x xs} (px : P x) → Any P xs → Any₂ P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any₂ P xs) → Any₂ P (x ∷ xs)

-- | A predicate stating any two predicates in the list cannot be inhabitated for the same elements.
PairwiseDisjoint₁ : {a ℓ : Level} {A : Set a} → List (Pred A ℓ) → Set (a ⊔ ℓsuc ℓ)
PairwiseDisjoint₁ Ps = ∀ {x} → Any₂ (λ{P → P x}) Ps → ⊥

-- | A predicate stating any two binary relations in the list cannot be inhabitated for the same elements.
PairwiseDisjoint₂ : {a b ℓ : Level} {A : Set a} {B : Set b} → List (REL A B ℓ) → Set (a ⊔ b ⊔ ℓsuc ℓ)
PairwiseDisjoint₂ Rs = ∀ {x y} → Any₂ (λ{R → R x y}) Rs → ⊥


-- # Properties

module _ {a b ℓ₁ ℓ₂ : Level} {A : Set a} {B : Set b} {P : REL A B ℓ₁} {Q : REL A B ℓ₂} where

  -- | If P is disjoint with Q, then Q is surely also disjoint with P.
  disjoint₂-sym : Disjoint₂ P Q → Disjoint₂ Q P
  disjoint₂-sym disjointPQ x y [Q∩P]xy =
    let [P∩Q]xy = ⇔₂-apply-⊆₂ (∩₂-comm {P = Q} {Q = P}) [Q∩P]xy
    in disjointPQ x y [P∩Q]xy


module _ {a b ℓ : Level} {A : Set a} {B : Set b} {P : REL A B ℓ} where

  -- | Every relation is disjoint with its negation.
  disjoint₂-neg : Disjoint₂ P (¬₂ P)
  disjoint₂-neg x y (Pxy , ¬Pxy) = ¬Pxy Pxy


module _ {a b ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set a} {B : Set b} {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL A B ℓ₃} where

  -- | If two relations P and Q are disjoint, then any subset R of P is also disjoint with Q.
  disjoint₂-⊆ˡ : R ⊆₂ P → Disjoint₂ P Q → Disjoint₂ R Q
  disjoint₂-⊆ˡ R⊆P disjointPQ x y [R∩Q]xy = disjointPQ x y (⊆₂-apply (∩₂-substˡ-⊆₂ {R = Q} R⊆P) [R∩Q]xy)

  -- | If two relations P and Q are disjoint, then any subset R of Q is also disjoint with P.
  disjoint₂-⊆ʳ : R ⊆₂ Q → Disjoint₂ P Q → Disjoint₂ P R
  disjoint₂-⊆ʳ R⊆Q disjointPQ x y [P∩R]xy = disjointPQ x y (⊆₂-apply (∩₂-substʳ-⊆₂ {R = P} R⊆Q) [P∩R]xy)
