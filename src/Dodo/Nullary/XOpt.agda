{-# OPTIONS --without-K --safe #-}


-- | Exclusive option. Exactly one of the options holds at the same time.
module Dodo.Nullary.XOpt where

-- Stdlib imports
open import Level using (Level; _⊔_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)


-- # XOpt₂

data XOpt₂ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  xopt₁ : ( a :   A) → (¬b : ¬ B) → XOpt₂ A B
  xopt₂ : (¬a : ¬ A) → ( b :   B) → XOpt₂ A B

xopt₂-apply : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
  → ( A → C )
  → ( B → C )
    -----------------
  → ( XOpt₂ A B → C )
xopt₂-apply f g (xopt₁ a _) = f a
xopt₂-apply f g (xopt₂ _ b) = g b

xopt₂-dec₁ : {a b : Level} {A : Set a} {B : Set b} → XOpt₂ A B → Dec A
xopt₂-dec₁ (xopt₁  a ¬b) = yes a
xopt₂-dec₁ (xopt₂ ¬a  b) = no ¬a

xopt₂-dec₂ : {a b : Level} {A : Set a} {B : Set b} → XOpt₂ A B → Dec B
xopt₂-dec₂ (xopt₁  a ¬b) = no ¬b
xopt₂-dec₂ (xopt₂ ¬a  b) = yes b

xopt₂-elim₁ : {a b : Level} {A : Set a} {B : Set b} → ¬ A → XOpt₂ A B → B
xopt₂-elim₁ ¬a (xopt₁  a ¬b) = ⊥-elim (¬a a)
xopt₂-elim₁ _  (xopt₂ ¬a  b) = b

xopt₂-elim₂ : {a b : Level} {A : Set a} {B : Set b} → ¬ B → XOpt₂ A B → A
xopt₂-elim₂ _  (xopt₁  a ¬b) = a
xopt₂-elim₂ ¬b (xopt₂ ¬a  b) = ⊥-elim (¬b b)

xopt₂-select₁ : {a b : Level} {A : Set a} {B : Set b} → A → XOpt₂ A B → ¬ B
xopt₂-select₁ _ (xopt₁ _ ¬b) = ¬b
xopt₂-select₁ a (xopt₂ ¬a _) = ⊥-elim (¬a a)

xopt₂-select₂ : {a b : Level} {A : Set a} {B : Set b} → B → XOpt₂ A B → ¬ A
xopt₂-select₂ b (xopt₁ _ ¬b) = ⊥-elim (¬b b)
xopt₂-select₂ b (xopt₂ ¬a _) = ¬a

xopt₂-sum : {a b : Level} {A : Set a} {B : Set b} → XOpt₂ A B → A ⊎ B
xopt₂-sum (xopt₁ a _) = inj₁ a
xopt₂-sum (xopt₂ _ b) = inj₂ b


-- # XOpt₃

data XOpt₃ {a b c : Level} (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
  xopt₁ : ( a :   A) → (¬b : ¬ B) → (¬c : ¬ C) → XOpt₃ A B C
  xopt₂ : (¬a : ¬ A) → ( b :   B) → (¬c : ¬ C) → XOpt₃ A B C
  xopt₃ : (¬a : ¬ A) → (¬b : ¬ B) → ( c :   C) → XOpt₃ A B C

xopt₃-apply : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  → ( A → D )
  → ( B → D )
  → ( C → D )
    -------------------
  → ( XOpt₃ A B C → D )
xopt₃-apply f g h (xopt₁ a _ _) = f a
xopt₃-apply f g h (xopt₂ _ b _) = g b
xopt₃-apply f g h (xopt₃ _ _ c) = h c

xopt₃-dec₁ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → XOpt₃ A B C → Dec A
xopt₃-dec₁ (xopt₁  a _ _) = yes  a
xopt₃-dec₁ (xopt₂ ¬a _ _) = no ¬a
xopt₃-dec₁ (xopt₃ ¬a _ _) = no ¬a

xopt₃-dec₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → XOpt₃ A B C → Dec B
xopt₃-dec₂ (xopt₁ _ ¬b _) = no ¬b
xopt₃-dec₂ (xopt₂ _  b _) = yes b
xopt₃-dec₂ (xopt₃ _ ¬b _) = no ¬b

xopt₃-dec₃ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → XOpt₃ A B C → Dec C
xopt₃-dec₃ (xopt₁ _ _ ¬c) = no ¬c
xopt₃-dec₃ (xopt₂ _ _ ¬c) = no ¬c
xopt₃-dec₃ (xopt₃ _ _  c) = yes c

xopt₃-elim₁ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → ¬ A → XOpt₃ A B C → XOpt₂ B C
xopt₃-elim₁ ¬a (xopt₁ a  _  _) = ⊥-elim (¬a a)
xopt₃-elim₁ _  (xopt₂ _  b ¬c) = xopt₁  b ¬c
xopt₃-elim₁ _  (xopt₃ _ ¬b  c) = xopt₂ ¬b  c

xopt₃-elim₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → ¬ B → XOpt₃ A B C → XOpt₂ A C
xopt₃-elim₂ ¬b (xopt₁  a  _ ¬c) = xopt₁  a ¬c
xopt₃-elim₂ ¬b (xopt₂  _  b  _) = ⊥-elim (¬b b)
xopt₃-elim₂ ¬b (xopt₃ ¬a  _  c) = xopt₂ ¬a  c

xopt₃-elim₃ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → ¬ C → XOpt₃ A B C → XOpt₂ A B
xopt₃-elim₃ _  (xopt₁  a ¬b  _) = xopt₁  a ¬b
xopt₃-elim₃ _  (xopt₂ ¬a  b  _) = xopt₂ ¬a  b
xopt₃-elim₃ ¬c (xopt₃  _  _  c) = ⊥-elim (¬c c)

xopt₃-select₁ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A → XOpt₃ A B C → ¬ B × ¬ C
xopt₃-select₁ a (xopt₁  _ ¬b ¬c) = ¬b , ¬c
xopt₃-select₁ a (xopt₂ ¬a  _  _) = ⊥-elim (¬a a)
xopt₃-select₁ a (xopt₃ ¬a  _  _) = ⊥-elim (¬a a)

xopt₃-select₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → B → XOpt₃ A B C → ¬ A × ¬ C
xopt₃-select₂ b (xopt₁  _ ¬b  _) = ⊥-elim (¬b b)
xopt₃-select₂ b (xopt₂ ¬a  _ ¬c) = ¬a , ¬c
xopt₃-select₂ b (xopt₃  _ ¬b  _) = ⊥-elim (¬b b)

xopt₃-select₃ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → C → XOpt₃ A B C → ¬ A × ¬ B
xopt₃-select₃ c (xopt₁  _  _ ¬c) = ⊥-elim (¬c c)
xopt₃-select₃ c (xopt₂  _  _ ¬c) = ⊥-elim (¬c c)
xopt₃-select₃ c (xopt₃ ¬a ¬b  _) = ¬a , ¬b

xopt₃-select₁₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A → B → XOpt₃ A B C → ⊥
xopt₃-select₁₂ a b x = proj₁ (xopt₃-select₁ a x) b

xopt₃-select₂₃ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → B → C → XOpt₃ A B C → ⊥
xopt₃-select₂₃ b c x = proj₂ (xopt₃-select₂ b x) c

xopt₃-select₁₃ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A → C → XOpt₃ A B C → ⊥
xopt₃-select₁₃ a c x = proj₂ (xopt₃-select₁ a x) c

xopt₃-sum : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → XOpt₃ A B C → A ⊎ B ⊎ C
xopt₃-sum (xopt₁ a _ _) = inj₁ a
xopt₃-sum (xopt₂ _ b _) = inj₂ (inj₁ b)
xopt₃-sum (xopt₃ _ _ c) = inj₂ (inj₂ c)
