{-# OPTIONS --without-K --safe #-}

module Dodo.Binary.SplittableOrder where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; REL; Transitive; Trichotomous; Tri; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_)
-- Local imports
open import Dodo.Unary.Equality
open import Dodo.Binary.Equality
open import Dodo.Binary.Immediate
open import Dodo.Binary.Trichotomous
open import Dodo.Binary.Transitive
open import Dodo.Binary.Domain
open import Dodo.Binary.Filter

open import Function using (flip)

-- # Definitions #

-- For any `R x y` there exists a /path/ from `x` to `y`.
SplittableOrder : {a ℓ : Level} {A : Set a} (R : Rel A ℓ) → Set (a ⊔ ℓ)
SplittableOrder R = R ⇔₂ TransClosure (immediate R)


-- # Properties #

module _ {a ℓ : Level} {A : Set a} {R : Rel A ℓ} where

  splittable-trans : SplittableOrder R → Transitive R
  splittable-trans splitR Rij Rjk = 
    ⇔₂-apply-⊇₂ splitR (⇔₂-apply-⊆₂ splitR Rij ++ ⇔₂-apply-⊆₂ splitR Rjk)


  splittable-flip : SplittableOrder R → SplittableOrder (flip R)
  splittable-flip splitR = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : flip R ⊆₂' TransClosure (immediate (flip R))
    ⊆-proof _ _ = ⁺-map _ imm-flip ∘ ⁺-flip ∘ ⇔₂-apply-⊆₂ splitR

    ⊇-proof : TransClosure (immediate (flip R)) ⊆₂' flip R
    ⊇-proof _ _ = ⇔₂-apply-⊇₂ splitR ∘ ⁺-flip ∘ ⁺-map _ imm-flip
    


-- # Operations #

-- Split the left-most element from the ordered relation chain
splitˡ : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → SplittableOrder R
  → {x y : A}
  → R x y
    --------------------------------------------------
  → immediate R x y ⊎ ∃[ z ] (immediate R x z × R z y)
splitˡ splitR Rxy with ⇔₂-apply-⊆₂ splitR Rxy
... | [ immRxy ] = inj₁ immRxy
... | _∷_ {x} {z} {y} immRxz immR⁺zy = inj₂ (z , immRxz , ⇔₂-apply-⊇₂ splitR immR⁺zy)


-- Split the right-most element from the ordered relation chain
splitʳ : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → SplittableOrder R
  → {x y : A}
  → R x y
    --------------------------------------------------
  → immediate R x y ⊎ ∃[ z ] (R x z × immediate R z y)
splitʳ {A = A} {R = R} splitR Rxy = lemma (⇔₂-apply-⊆₂ splitR Rxy)
  where
  lemma : ∀ {x y : A} → TransClosure (immediate R) x y → immediate R x y ⊎ ∃[ z ] (R x z × immediate R z y)
  lemma [ immRxy ] = inj₁ immRxy
  lemma ( _∷_ {x} {z} {y} immRxz immR⁺zy ) with lemma immR⁺zy
  ... | inj₁ immRzy = inj₂ (z , proj₁ immRxz , immRzy)
  ... | inj₂ (w , Rzw , immRwy) = inj₂ (w , splittable-trans splitR (proj₁ immRxz) Rzw , immRwy)


-- Splits the given left-most element from the chain.
unsplitˡ : ∀ {a ℓ₁ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂}
  → Trichotomous _≈_ R
  → SplittableOrder R
  → {x y z : A}
  → R x z
  → immediate R x y
  → y ≈ z ⊎ R y z
unsplitˡ triR splitR {x} {y} {z} Rxz immRxy with splitˡ splitR Rxz
unsplitˡ triR splitR {x} {y} {z} Rxz immRxy | inj₁ immRxz = inj₁ (tri-immʳ triR immRxy immRxz)
unsplitˡ triR splitR {x} {y} {z} Rxz immRxy | inj₂ (v , immRxv , Rvz) with triR y z
unsplitˡ triR splitR {x} {y} {z} Rxz immRxy | inj₂ (v , immRxv , Rvz) | tri<  Ryz y≢z ¬Rzy = inj₂ Ryz
unsplitˡ triR splitR {x} {y} {z} Rxz immRxy | inj₂ (v , immRxv , Rvz) | tri≈ ¬Ryz y≡z ¬Rzy = inj₁ y≡z
unsplitˡ triR splitR {x} {y} {z} Rxz immRxy | inj₂ (v , immRxv , Rvz) | tri> ¬Ryz y≢z  Rzy = ⊥-elim (proj₂ immRxy (z , Rxz , [ Rzy ]))


-- Splits the given right-most element from the chain.
unsplitʳ : ∀ {a ℓ₁ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ₁} {R : Rel A ℓ₂}
  → Trichotomous _≈_ R
  → SplittableOrder R
  → {x y z : A}
  → R x z
  → immediate R y z
  → x ≈ y ⊎ R x y
unsplitʳ triR splitR {x} {y} {z} Rxz iRyz with splitʳ splitR Rxz
unsplitʳ triR splitR {x} {y} {z} Rxz iRyz | inj₁ iRxz = inj₁ (tri-immˡ triR iRxz iRyz)
unsplitʳ triR splitR {x} {y} {z} Rxz iRyz | inj₂ (v , Rxv , iRvz) with triR x y
unsplitʳ triR splitR {x} {y} {z} Rxz iRyz | inj₂ (v , Rxv , iRvz) | tri<  Rxy x≢y ¬Ryx = inj₂ Rxy
unsplitʳ triR splitR {x} {y} {z} Rxz iRyz | inj₂ (v , Rxv , iRvz) | tri≈ ¬Rxy x≡y ¬Ryx = inj₁ x≡y
unsplitʳ triR splitR {x} {y} {z} Rxz iRyz | inj₂ (v , Rxv , iRvz) | tri> ¬Rxy x≢y  Ryx = ⊥-elim (proj₂ iRyz (x , Ryx , [ Rxz ]))


splittable-imm-udr : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → SplittableOrder R
  → udr R ⇔₁ udr (immediate R)
splittable-imm-udr {R = R} splitR = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : udr R ⊆₁' udr (immediate R)
  ⊆-proof x (inj₁ (y , Rxy)) = inj₁ (⁺-dom (⇔₂-apply-⊆₂ splitR Rxy))
  ⊆-proof y (inj₂ (x , Rxy)) = inj₂ (⁺-codom (⇔₂-apply-⊆₂ splitR Rxy))

  ⊇-proof : udr (immediate R) ⊆₁' udr R
  ⊇-proof x (inj₁ (y , Rxy)) = inj₁ (y , proj₁ Rxy)
  ⊇-proof y (inj₂ (x , Rxy)) = inj₂ (x , proj₁ Rxy)


-- | If any value in the chain of R satisfies P, it remains splittable after lifting.
--
-- The chain is traversed /to the left/.
filter-splittableˡ : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → SplittableOrder R
  → (P : Pred A ℓ)
  → (∀ {x y : A} → P y → R x y → P x)
    ---------------------------------
  → SplittableOrder (filter-rel P R)
filter-splittableˡ {A = A} {R = R} splitR P f = ⇔: ⊆-proof ⊇-proof
  where
  lemma⊆-imm : ∀ {x y : A} → (Px : P x) → (Py : P y) → immediate R x y → immediate (filter-rel P R) (with-pred x Px) (with-pred y Py)
  lemma⊆-imm {x} {y} Px Py (Rxy , ¬∃z) = Rxy , ¬∃z'
    where
    ¬∃z' : ¬ (∃[ z ] filter-rel P R (with-pred x Px) z × TransClosure (filter-rel P R) z (with-pred y Py))
    ¬∃z' (with-pred z Pz , Rxz , R⁺zy) = ¬∃z (z , Rxz , ⁺-strip-filter R⁺zy)

  lemma⊆ : ∀ {x y : A} → (Px : P x) → (Py : P y) → TransClosure (immediate R) x y
    → TransClosure (immediate (filter-rel P R)) (with-pred x Px) (with-pred y Py)
  lemma⊆ Px Py [ iRxy ] = [ lemma⊆-imm Px Py iRxy ]
  lemma⊆ Px Py ( iRxz ∷ iR⁺zy ) =
    let Pz = ⁺-predˡ (λ Pz → f Pz ∘ proj₁) iR⁺zy Py
    in lemma⊆-imm Px Pz iRxz ∷ lemma⊆ Pz Py iR⁺zy

  ⊆-proof : filter-rel P R ⊆₂' TransClosure (immediate (filter-rel P R))
  ⊆-proof (with-pred x Px) (with-pred y Py) Rxy = lemma⊆ Px Py (⇔₂-apply-⊆₂ splitR Rxy)

  lemma⊇-imm : ∀ {x y : A} → (Px : P x) → (Py : P y) → immediate (filter-rel P R) (with-pred x Px) (with-pred y Py)
    → immediate R x y
  lemma⊇-imm {x} {y} Px Py (Rxy , ¬∃z) = (Rxy , ¬∃z')
    where
    ¬∃z' : ¬ (∃[ z ] R x z × TransClosure R z y)
    ¬∃z' (z , Rxz , R⁺zy) =
      let Pz = ⁺-predˡ f R⁺zy Py
      in ¬∃z (with-pred z Pz , Rxz , ⁺-filter-relˡ f Pz Py R⁺zy)
    
  lemma⊇ : ∀ {x y : A} → (Px : P x) → (Py : P y)
    → TransClosure (immediate (filter-rel P R)) (with-pred x Px) (with-pred y Py)
    → TransClosure (immediate R) x y
  lemma⊇ Px Py [ iRxy ] = [ lemma⊇-imm Px Py iRxy ]
  lemma⊇ Px Py ( _∷_ {_} {with-pred z Pz} iRxz iR⁺zy ) = lemma⊇-imm Px Pz iRxz ∷ lemma⊇ Pz Py iR⁺zy
    
  ⊇-proof : TransClosure (immediate (filter-rel P R)) ⊆₂' filter-rel P R
  ⊇-proof (with-pred x Px) (with-pred y Py) Rxy = ⇔₂-apply-⊇₂ splitR (lemma⊇ Px Py Rxy)
  

-- | If any value in the chain of R satisfies P, it remains splittable after lifting.
--
-- The chain is traversed /to the right/.
filter-splittableʳ : ∀ {a ℓ : Level} {A : Set a} {R : Rel A ℓ}
  → SplittableOrder R
  → (P : Pred A ℓ)
  → (∀ {x y : A} → P x → R x y → P y)
    ---------------------------------
  → SplittableOrder (filter-rel P R)
filter-splittableʳ {A = A} {R = R} splitR P f = ⇔: ⊆-proof ⊇-proof
  where
  lemma⊆-imm : ∀ {x y : A} → (Px : P x) → (Py : P y) → immediate R x y → immediate (filter-rel P R) (with-pred x Px) (with-pred y Py)
  lemma⊆-imm {x} {y} Px Py (Rxy , ¬∃z) = Rxy , ¬∃z'
    where
    ¬∃z' : ¬ (∃[ z ] filter-rel P R (with-pred x Px) z × TransClosure (filter-rel P R) z (with-pred y Py))
    ¬∃z' (with-pred z Pz , Rxz , R⁺zy) = ¬∃z (z , Rxz , ⁺-strip-filter R⁺zy)

  lemma⊆ : ∀ {x y : A} → (Px : P x) → (Py : P y) → TransClosure (immediate R) x y
    → TransClosure (immediate (filter-rel P R)) (with-pred x Px) (with-pred y Py)
  lemma⊆ Px Py [ iRxy ] = [ lemma⊆-imm Px Py iRxy ]
  lemma⊆ Px Py ( iRxz ∷ iR⁺zy ) =
    let Pz = f Px (proj₁ iRxz)
    in lemma⊆-imm Px Pz iRxz ∷ lemma⊆ Pz Py iR⁺zy

  ⊆-proof : filter-rel P R ⊆₂' TransClosure (immediate (filter-rel P R))
  ⊆-proof (with-pred x Px) (with-pred y Py) Rxy = lemma⊆ Px Py (⇔₂-apply-⊆₂ splitR Rxy)

  lemma⊇-imm : ∀ {x y : A} → (Px : P x) → (Py : P y) → immediate (filter-rel P R) (with-pred x Px) (with-pred y Py)
    → immediate R x y
  lemma⊇-imm {x} {y} Px Py (Rxy , ¬∃z) = Rxy , ¬∃z'
    where
    ¬∃z' : ¬ (∃[ z ] R x z × TransClosure R z y)
    ¬∃z' (z , Rxz , R⁺zy) =
      let Pz = f Px Rxz
      in ¬∃z (with-pred z Pz , Rxz , ⁺-filter-relʳ f Pz Py R⁺zy)
    
  lemma⊇ : ∀ {x y : A} → (Px : P x) → (Py : P y)
    → TransClosure (immediate (filter-rel P R)) (with-pred x Px) (with-pred y Py)
    → TransClosure (immediate R) x y
  lemma⊇ Px Py [ iRxy ] = [ lemma⊇-imm Px Py iRxy ]
  lemma⊇ Px Py ( _∷_ {_} {with-pred z Pz} iRxz iR⁺zy ) = lemma⊇-imm Px Pz iRxz ∷ lemma⊇ Pz Py iR⁺zy
    
  ⊇-proof : TransClosure (immediate (filter-rel P R)) ⊆₂' filter-rel P R
  ⊇-proof (with-pred x Px) (with-pred y Py) Rxy = ⇔₂-apply-⊇₂ splitR (lemma⊇ Px Py Rxy)
