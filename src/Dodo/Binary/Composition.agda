{-# OPTIONS --without-K --safe #-}

-- | Functions for the composition of binary relations.
module Dodo.Binary.Composition where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Function.Base using (flip)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Transitive; Symmetric)
-- Local imports
open import Dodo.Binary.Equality


private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A B C D : Set a


-- # Definitions

infixl 10 _⨾_ ⨾:

-- | Composition of binary relations.
--
-- The composition of two relations P and Q, is mathematically denoted as `P⨾Q`. It is
-- inhabited as `(P⨾Q) x y`, iff `P x z` and `Q z y` are inhabited, for some `z`.
--
-- The notation used here is:
-- > Pxz ⨾[ z ]⨾ Qzy : (P ⨾ Q) x y
--
-- Where the corresponding types are:
-- > Pxz : P x z
-- > Qzy : Q z y
--
-- That notation is syntactic sugar for the constructor below:
-- > ⨾: z Pxz Qzy
--
--
-- # Design decision: Syntactic sugar with explicit `z`
--
-- The syntactic sugar /cannot/ be the actual constructor, as `Pxz` depends on `z`; Meaning
-- that Agda requires to know `z` before `Pxz`. Alternatively, `z` could be /implicit/
-- (as it is in the standard library). For instance:
-- > Pxz ⨾ Qzy : (P ⨾ Q) x y
--
-- The disadvantage of that approach is that `z` may not always be inferred from `Pxz` and `Qzy`.
-- After all, `Pxz` and `Qzy` may be beta-reduced, for which different types of `P`, `Q`, `x`, `y`,
-- and `z` hold; Which introduces ambiguity during type checking. This, in turn, requires making
-- the implicit argument /explicit/ in practice; namely:
-- > _⨾_  {z} Pxz Qzy
--
-- Which is syntactically even less desirable. Hence, in the definition below, `z` is represented
-- explicitly.
data _⨾_ {A : Set a} {B : Set b} {C : Set c} (L : REL A B ℓ₁) (R : REL B C ℓ₂)
    (i : A) (j : C) : Set (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂) where
  ⨾: : (k : B) → L i k → R k j → (L ⨾ R) i j

syntax ⨾: k Pik Qkj = Pik ⨾[ k ]⨾ Qkj


-- # Properties

module _ {P : REL A B ℓ₁} {Q : REL B C ℓ₂} {R : REL C D ℓ₃} where

  -- | Composition of binary relations is associative.
  ⨾-assoc : (P ⨾ Q) ⨾ R ⇔₂ P ⨾ (Q ⨾ R)
  ⨾-assoc = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : (P ⨾ Q) ⨾ R ⊆₂' P ⨾ (Q ⨾ R)
    ⊆-proof _ _ ((Pxb ⨾[ b ]⨾ Qbc) ⨾[ c ]⨾ Rcy) = Pxb ⨾[ b ]⨾ (Qbc ⨾[ c ]⨾ Rcy)
    ⊇-proof : P ⨾ (Q ⨾ R) ⊆₂' (P ⨾ Q) ⨾ R
    ⊇-proof _ _ (Pxb ⨾[ b ]⨾ (Qbc ⨾[ c ]⨾ Rcy)) = (Pxb ⨾[ b ]⨾ Qbc) ⨾[ c ]⨾ Rcy


module _ {R : Rel A ℓ₁} where

  -- | The composition of a transitive relation with itself is a subset of itself.
  ⨾-trans-⊆₂ : Transitive R → (R ⨾ R) ⊆₂ R
  ⨾-trans-⊆₂ transR = ⊆: lemma
    where
    lemma : (R ⨾ R) ⊆₂' R
    lemma _ _ (Rxz ⨾[ z ]⨾ Rzy) = transR Rxz Rzy


-- # Operations

module _ {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL B C ℓ₃} where

  ⨾-substˡ-⊆₂ : P ⊆₂ Q → (P ⨾ R) ⊆₂ (Q ⨾ R)
  ⨾-substˡ-⊆₂ (⊆: P⊆Q) = ⊆: ⊆-proof
    where
    ⊆-proof : (P ⨾ R) ⊆₂' (Q ⨾ R)
    ⊆-proof x y (Pxz ⨾[ z ]⨾ Rzy) = P⊆Q x z Pxz ⨾[ z ]⨾ Rzy


module _ {P : REL A B ℓ₁} {Q : REL A B ℓ₂} {R : REL B C ℓ₃} where
    
  ⨾-substˡ : P ⇔₂ Q → (P ⨾ R) ⇔₂ (Q ⨾ R)
  ⨾-substˡ = ⇔₂-compose ⨾-substˡ-⊆₂ ⨾-substˡ-⊆₂


module _ {P : REL B C ℓ₁} {Q : REL B C ℓ₂} {R : REL A B ℓ₃} where
    
  ⨾-substʳ-⊆₂ : P ⊆₂ Q → (R ⨾ P) ⊆₂ (R ⨾ Q)
  ⨾-substʳ-⊆₂ (⊆: P⊆Q) = ⊆: ⊆-proof
    where
    ⊆-proof : (R ⨾ P) ⊆₂' (R ⨾ Q)
    ⊆-proof x y (Rxz ⨾[ z ]⨾ Pzy) = Rxz ⨾[ z ]⨾ P⊆Q z y Pzy


module _ {P : REL B C ℓ₁} {Q : REL B C ℓ₂} {R : REL A B ℓ₃} where
    
  ⨾-substʳ : P ⇔₂ Q → (R ⨾ P) ⇔₂ (R ⨾ Q)
  ⨾-substʳ = ⇔₂-compose ⨾-substʳ-⊆₂ ⨾-substʳ-⊆₂


module _ {P : REL A B ℓ₁} {Q : REL B C ℓ₂} where

  -- | Expanded definition of flipping the composition of two relations.
  ⨾-flip : flip (P ⨾ Q) ⇔₂ flip Q ⨾ flip P
  ⨾-flip = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : flip (P ⨾ Q) ⊆₂' flip Q ⨾ flip P
    ⊆-proof x y (Pyz ⨾[ z ]⨾ Qzx) = (Qzx ⨾[ z ]⨾ Pyz)
    ⊇-proof : flip Q ⨾ flip P ⊆₂' flip (P ⨾ Q)
    ⊇-proof x y (Qzy ⨾[ z ]⨾ Pxz) = (Pxz ⨾[ z ]⨾ Qzy)
