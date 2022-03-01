# Dodo: A library for relations in Agda

Dodo relies upon the definitions of relations in Agda's standard library, but extends it with many more lemmas.

## Setting Up

* [Install Agda (v.2.6.2)](https://agda.readthedocs.io/en/v2.6.2/getting-started/installation.html) with its standard library
* Make sure Agda can find the standard library (see the `~/.agda/libraries` and `~/.agda/defaults` files in the installation instructions)

> :warning: The proofs were developed with standard library version 1.7.1. Other versions may be incompatible.

## Using

Most likely, you want to use the `Dodo.Binary` module; It contains lemmas for proofs on binary relations.
The other top level modules are `Dodo.Unary` and `Dodo.Nullary`.

### Example proof on Binary Relations

```agda
-- Stdlib imports
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (REL)
-- Dodo library imports
open import Dodo.Binary

proof : ∀ {A B C D E : Set}
    (P : REL A B ℓ₀)
  → (Q : REL B C ℓ₀)
  → (R : REL C D ℓ₀)
  → (S : REL D E ℓ₀)
    ------------------------------------
  → (P ⨾ Q) ⨾ (R ⨾ S) ⇔₂ P ⨾ (Q ⨾ R) ⨾ S
proof P Q R S =
  begin⇔₂
    (P ⨾ Q) ⨾ (R ⨾ S)
  ⇔₂⟨ ⇔₂-sym ⨾-assoc ⟩
    ((P ⨾ Q) ⨾ R) ⨾ S
  ⇔₂⟨ ⨾-substˡ ⨾-assoc ⟩
    P ⨾ (Q ⨾ R) ⨾ S
  ⇔₂∎
```

### Example proof on cycles

```agda
-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using () renaming (zero to ℓ₀)
open import Data.Empty using (⊥)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Dodo library imports
open import Dodo.Binary

proof : {A : Set} {R : Rel A ℓ₀}
  → Acyclic _≡_ R
  → {x y z : A}
  → R x y → R y z → R z x
  → ⊥
proof acyclicR Rxy Ryz Rzx = acyclicR refl ( Rxy ∷ Ryz ∷ [ Rzx ] )
```


## License

BSD-3
