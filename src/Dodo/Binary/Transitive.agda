{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Transitive where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Level using (Level; _⊔_)
open import Function using (flip; _∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Transitive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _∷ʳ_; _++_)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Binary.Equality
open import Dodo.Binary.Domain


private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A : Set a


⁺-flip : {R : Rel A ℓ}
  → {x y : A}
  → TransClosure R x y
  → TransClosure (flip R) y x
⁺-flip [ x∼y ]      = [ x∼y ]
⁺-flip (x∼z ∷ z∼⁺y) = ⁺-flip z∼⁺y ∷ʳ x∼z

⁺-map : {A : Set a} {B : Set b}
  → {R : Rel A ℓ₁} {Q : Rel B ℓ₂}
  → (f : A → B)
  → (map : ∀ {x y : A} → R x y → Q (f x) (f y))
  → {x y : A}
  → TransClosure R x y
  → TransClosure Q (f x) (f y)
⁺-map _ map [ Rxy ] = [ map Rxy ]
⁺-map _ map ( Rxz ∷ R⁺zy ) = map Rxz ∷ ⁺-map _ map R⁺zy

⁺-dom : {R : Rel A ℓ}
  → {x y : A}
  → TransClosure R x y
    ------------------
  → x ∈ dom R
⁺-dom {R = R} [ Rxy ] = take-dom R Rxy
⁺-dom {R = R} ( Rxz ∷ R⁺zy ) = take-dom R Rxz

⁺-codom : {R : Rel A ℓ}
  → {x y : A}
  → TransClosure R x y
    ------------------
  → y ∈ codom R
⁺-codom {R = R} [ Rxy ] = take-codom R Rxy
⁺-codom {R = R} ( Rxz ∷ R⁺zy ) = ⁺-codom R⁺zy

⁺-udrˡ : {R : Rel A ℓ}
  → {x y : A}
  → TransClosure R x y
    ------------------
  → x ∈ udr R
⁺-udrˡ = inj₁ ∘ ⁺-dom

⁺-udrʳ : {R : Rel A ℓ}
  → {x y : A}
  → TransClosure R x y
    ------------------
  → y ∈ udr R
⁺-udrʳ = inj₂ ∘ ⁺-codom

⁺-predʳ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → P x → R x y → P y)
  → {x y : A}
  → TransClosure R x y
  → P x
  → P y
⁺-predʳ f [ Rxy ]        Px = f Px Rxy
⁺-predʳ f ( Rxz ∷ R⁺zy ) Px = ⁺-predʳ f R⁺zy (f Px Rxz)

⁺-predˡ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → P y → R x y → P x)
  → {x y : A}
  → TransClosure R x y
  → P y
  → P x
⁺-predˡ f [ Rxy ]        Px = f Px Rxy
⁺-predˡ f ( Rxz ∷ R⁺zy ) Px = f (⁺-predˡ f R⁺zy Px) Rxz

⁺-lift-predʳ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → R x y → P y)
  → {x y : A}
  → TransClosure R x y
  → P y
⁺-lift-predʳ f [ Rxy ] = f Rxy
⁺-lift-predʳ f ( Rxz ∷ R⁺zy ) = ⁺-lift-predʳ f R⁺zy

⁺-lift-predˡ : {P : Pred A ℓ₁} {R : Rel A ℓ₂}
  → (f : ∀ {x y : A} → R x y → P x)
  → {x y : A}
  → TransClosure R x y
  → P x
⁺-lift-predˡ f [ Rxy ] = f Rxy
⁺-lift-predˡ f ( Rxz ∷ R⁺zy ) = f Rxz


module _ {a ℓ : Level} {A : Set a} {R : Rel A ℓ} where

  ⁺-idem : TransClosure R ⇔₂ TransClosure (TransClosure R)
  ⁺-idem = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : TransClosure R ⊆₂' TransClosure (TransClosure R)
    ⊆-proof _ _ R⁺xy = [ R⁺xy ]
    
    ⊇-proof : TransClosure (TransClosure R) ⊆₂' TransClosure R
    ⊇-proof _ _ [ R⁺xy ] = R⁺xy
    ⊇-proof _ y ( _∷_ {_} {z} R⁺xz R⁺⁺zy ) = R⁺xz ++ ⊇-proof z y R⁺⁺zy

  ⁺-join : ∀ {x y : A} → TransClosure (TransClosure R) x y → TransClosure R x y
  ⁺-join = ⇔₂-apply-⊇₂ ⁺-idem


module _ {a ℓ : Level} {A : Set a} {R : Rel A ℓ} where

  ⁺-preserves-dom : dom R ⇔₁ dom (TransClosure R)
  ⁺-preserves-dom = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : dom R ⊆₁' dom (TransClosure R)
    ⊆-proof x (y , Rxy) = (y , [ Rxy ])

    ⊇-proof : dom (TransClosure R) ⊆₁' dom R
    ⊇-proof x (y , R⁺xy) = ⁺-dom R⁺xy

  ⁺-preserves-codom : codom R ⇔₁ codom (TransClosure R)
  ⁺-preserves-codom = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : codom R ⊆₁' codom (TransClosure R)
    ⊆-proof y (x , Rxy) = (x , [ Rxy ])

    ⊇-proof : codom (TransClosure R) ⊆₁' codom R
    ⊇-proof y (x , R⁺xy) = ⁺-codom R⁺xy

  ⁺-preserves-udr : udr R ⇔₁ udr (TransClosure R)
  ⁺-preserves-udr = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : udr R ⊆₁' udr (TransClosure R)
    ⊆-proof _ (inj₁ x∈dom)   = inj₁ (⇔₁-apply-⊆₁ ⁺-preserves-dom x∈dom)
    ⊆-proof _ (inj₂ x∈codom) = inj₂ (⇔₁-apply-⊆₁ ⁺-preserves-codom x∈codom)
    
    ⊇-proof : udr (TransClosure R) ⊆₁' udr R
    ⊇-proof _ (inj₁ x∈dom)   = inj₁ (⇔₁-apply-⊇₁ ⁺-preserves-dom x∈dom)
    ⊇-proof _ (inj₂ x∈codom) = inj₂ (⇔₁-apply-⊇₁ ⁺-preserves-codom x∈codom)


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  ⁺-preserves-⊆₂ : P ⊆₂ Q → TransClosure P ⊆₂ TransClosure Q
  ⁺-preserves-⊆₂ P⊆Q = ⊆: lemma
    where
    lemma : TransClosure P ⊆₂' TransClosure Q
    lemma _ _ [ Pxy ] = [ ⊆₂-apply P⊆Q Pxy ]
    lemma _ y ( _∷_ {_} {z} Pxz P⁺zy ) = ⊆₂-apply P⊆Q Pxz ∷ lemma z y P⁺zy


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  ⁺-preserves-⇔₂ : P ⇔₂ Q → TransClosure P ⇔₂ TransClosure Q
  ⁺-preserves-⇔₂ = ⇔₂-compose ⁺-preserves-⊆₂ ⁺-preserves-⊆₂


module _ {a ℓ : Level} {A : Set a} {R : Rel A ℓ} where

  ⁺-trans-⇔₂ : Transitive R → R ⇔₂ TransClosure R
  ⁺-trans-⇔₂ transR = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : R ⊆₂' TransClosure R
    ⊆-proof _ _ = [_]
    
    ⊇-proof : TransClosure R ⊆₂' R
    ⊇-proof _ _ [ Rxy ] = Rxy
    ⊇-proof _ y (_∷_ {_} {w} Rxw R⁺wy) = transR Rxw (⊇-proof w y R⁺wy)

  ⁺-trans-⊆₂ : Transitive R → TransClosure R ⊆₂ R
  ⁺-trans-⊆₂ transR = ⇔₂-to-⊇₂ (⁺-trans-⇔₂ transR)

  ⁺-join-trans : Transitive R → {x y : A} → TransClosure R x y → R x y
  ⁺-join-trans = ⊆₂-apply ∘ ⁺-trans-⊆₂

  ⁺-unconsʳ :
      {x y : A}
    → TransClosure R x y
    → R x y ⊎ ∃[ z ] (TransClosure R x z × R z y)
  ⁺-unconsʳ [ Rxy ] = inj₁ Rxy
  ⁺-unconsʳ ( Rxz ∷ R⁺zy ) with ⁺-unconsʳ R⁺zy
  ... | inj₁ Rzy = inj₂ (_ , [ Rxz ] , Rzy)
  ... | inj₂ (v , R⁺zv , Rvy) = inj₂ (v , Rxz ∷ R⁺zv , Rvy)
