{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.Immediate where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level; _⊔_)
open import Function using (_∘_; flip)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (IsStrictTotalOrder; Irreflexive; Trichotomous)
open import Relation.Binary using (Transitive)
open import Relation.Binary using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _∷ʳ_; _++_)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Unary.Unique
open import Dodo.Binary.Equality
open import Dodo.Binary.Transitive
open import Dodo.Binary.Functional
open import Dodo.Binary.Filter
open import Dodo.Binary.Domain


-- # Definitions #

-- | The immediate relation over the given (order) relation
immediate : ∀ {a ℓ : Level} {A : Set a}
  → Rel A ℓ
    -------------
  → Rel A (a ⊔ ℓ)
immediate r x y = r x y × ¬ (∃[ z ] r x z × TransClosure r z y)
-- A more conventional definitions is:
-- immediate r x y = r x y × (¬ ∃ λ{z → r x z × r z y})
-- which is identical to this one when r is Transitive


Immediate : ∀ {a ℓ : Level} {A : Set a}
  → Rel A ℓ
  → Set (a ⊔ ℓ)
-- For some reason, x and y have to be /explicit/. Otherwise, Agda complains about some
-- of Immediate's uses. Unsure why.
Immediate {A = A} r = ∀ (x y : A) → r x y → ¬ (∃[ z ] r x z × TransClosure r z y)


-- # Operations #

imm-flip : ∀ {a ℓ : Level} {A : Set a}
  → {R : Rel A ℓ} {x y : A}
  → immediate R x y
  → immediate (flip R) y x
imm-flip {R = R} {x} {y} (Rxy , ¬∃z) = (Rxy , lemma)
  where
  ⁺-invert : {a ℓ : Level} {A : Set a} {R : Rel A ℓ} {x y : A}
    → {z : A} → R x z → TransClosure R z y
    → ∃[ q ] (TransClosure R x q × R q y)
  ⁺-invert {z = z} Rxz [ Rzy ] = (z , [ Rxz ] , Rzy)
  ⁺-invert {z = z} Rxz ( Rzq ∷ R⁺qy ) with ⁺-invert Rzq R⁺qy
  ... | v , R⁺zv , Rvy = (v , Rxz ∷ R⁺zv , Rvy)

  lemma : ¬ (∃[ z ] (flip R y z × TransClosure (flip R) z x))
  lemma (z , flipRyz , flipR⁺zx) =
    let (q , R⁺yq , Rqx) = ⁺-invert flipRyz flipR⁺zx
    in ¬∃z (q , Rqx , ⁺-flip R⁺yq)


-- # Properties #

module _ {a ℓ : Level} {A : Set a} {R : Rel A ℓ} where

  imm-imm : Immediate (immediate R)
  imm-imm _ _ (Rxy , ¬∃z) (z , (Rxz , ¬∃w) , [immR]⁺xy) = ¬∃z (z , Rxz , ⁺-map _ proj₁ [immR]⁺xy)


  imm-⊆₂ : immediate R ⊆₂ R
  imm-⊆₂ = ⊆: λ{_ _ → proj₁}


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where

  imm-uniqueˡ : Trichotomous _≈_ _<_ → {z : A} → Unique₁ _≈_ λ{τ → immediate _<_ τ z}
  imm-uniqueˡ triR {z} {x} {y} (Rxz , ¬∃y) (Ryz , ¬∃x) with triR x y
  ... | tri<  Rxy x≉y ¬Ryx = ⊥-elim (¬∃y (y , Rxy , [ Ryz ]))
  ... | tri≈ ¬Rxy x≈y ¬Ryx = x≈y
  ... | tri> ¬Rxy x≉y  Ryx = ⊥-elim (¬∃x (x , Ryx , [ Rxz ]))

  imm-uniqueʳ : Trichotomous _≈_ _<_ → {x : A} → Unique₁ _≈_ (immediate _<_ x)
  imm-uniqueʳ triR {x} {y} {z} (Rxy , ¬∃z) (Rxz , ¬∃y) with triR y z
  ... | tri<  Ryz y≈z ¬Rzy = ⊥-elim (¬∃y (y , Rxy , [ Ryz ]))
  ... | tri≈ ¬Ryz y≈z ¬Rzy = y≈z
  ... | tri> ¬Ryz y≈z  Rzy = ⊥-elim (¬∃z (z , Rxz , [ Rzy ]))
  

module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {≈ : Rel A ℓ₁} {< : Rel A ℓ₂} where

  -- immediate < x y → immediate < x z → y ≈ z
  imm-func : IsStrictTotalOrder ≈ < → Functional ≈ (immediate <)
  imm-func sto x y₁ y₂ (x<y₁ , ¬∃z[x<z×z<y₁]) (x<y₂ , ¬∃z[x<z×z<y₂])
      with IsStrictTotalOrder.compare sto y₁ y₂
  ... | tri< y₁<y₂ _     _     = ⊥-elim (¬∃z[x<z×z<y₂] (y₁ , x<y₁ , [ y₁<y₂ ]))
  ... | tri≈ _     y₁≈y₂ _     = y₁≈y₂
  ... | tri> _     _     y₂<y₁ = ⊥-elim (¬∃z[x<z×z<y₁] (y₂ , x<y₂ , [ y₂<y₁ ]))


module _ {a ℓ₁ ℓ₂ : Level} {A : Set a} {P : Pred A ℓ₁} {R : Rel A ℓ₂} where

  imm-filter-⊆₂ : filter-rel P (immediate R) ⊆₂ immediate (filter-rel P R)
  imm-filter-⊆₂ = ⊆: lemma
    where
    lemma : filter-rel P (immediate R) ⊆₂' immediate (filter-rel P R)
    lemma (with-pred x Px) (with-pred y Py) (Rxy , ¬∃z) = Rxy , ¬∃z'
      where
      ¬∃z' : ¬ (∃[ z ] (filter-rel P R (with-pred x Px) z × TransClosure (filter-rel P R) z (with-pred y Py)))
      ¬∃z' (with-pred z Pz , Rxz , fR⁺zy) = ¬∃z (z , Rxz , ⁺-strip-filter fR⁺zy)
      

module _ {a ℓ : Level} {A : Set a} {R : Rel A ℓ} where

  immediate⁺ : Immediate R → R ⇔₂ immediate (TransClosure R)
  immediate⁺ immR = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : R ⊆₂' immediate (TransClosure R)
    ⊆-proof x y xRy = ([ xRy ] , lemma x y xRy)
      where
      lemma : (x y : A) → R x y → ¬ (∃[ z ] TransClosure R x z × TransClosure (TransClosure R) z y)
      lemma x y xRy (z , [ xRz ] , zR⁺y) =
        immR x y xRy (z , xRz , ⇔₂-apply-⊇₂ ⁺-idem zR⁺y)
      lemma x y xRy (z , _∷_ {_} {w} xRw wR⁺z , zR⁺y) =
        immR x y xRy (w , xRw , ⇔₂-apply-⊇₂ ⁺-idem (wR⁺z ∷ zR⁺y))

    ⊇-proof : immediate (TransClosure R) ⊆₂' R
    ⊇-proof x y ([ x∼y ] , ¬∃z) = x∼y
    ⊇-proof x y (_∷_ {_} {w} x∼w wR⁺y , ¬∃z) = ⊥-elim (¬∃z (w , [ x∼w ] , [ wR⁺y ]))


  trans-imm⁺-⊆ : Transitive R → TransClosure (immediate R) ⊆₂ R
  trans-imm⁺-⊆ transR = ⊆: lemma
    where
    lemma : TransClosure (immediate R) ⊆₂' R
    lemma x y [ R[xy] ] = proj₁ R[xy]
    lemma x y (_∷_ {_} {z} R[xz] R⁺[zy]) = transR (proj₁ R[xz]) (lemma z y R⁺[zy])


  imm-udr-⊆₁ : udr (immediate R) ⊆₁ udr R
  imm-udr-⊆₁ = ⊆: lemma
    where
    lemma : udr (immediate R) ⊆₁' udr R
    lemma _ (inj₁ (y , Rxy , ¬∃z)) = inj₁ (y , Rxy)
    lemma _ (inj₂ (x , Rxy , ¬∃z)) = inj₂ (x , Rxy)
