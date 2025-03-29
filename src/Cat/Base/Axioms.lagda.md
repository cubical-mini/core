```agda

module Cat.Base.Axioms where

open import Prim.Prelude renaming ( _∘_ to _*_ )
open import Lib.Path.Base
open import Lib.Equiv.Base

open import Data.Semicategory.Base

```

Recall the definition of a Semicategory

record Semicategory o h : Type₊ (o ⊔ h) where
  infixr 40 _∘_
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
          → (h ∘ g) ∘ f ＝ h ∘ (g ∘ f)

```

module _ {o h} (S : Semicategory o h) where
  open Semicategory S

  is-left-inverse : ∀ {x y} → Hom x y → Type (o ⊔ h)
  is-left-inverse {x} g = {w : Ob} → is-equiv (λ (f : Hom w x) → g ∘ f)

  is-right-inverse : ∀ {x y} → Hom x y → Type (o ⊔ h)
  is-right-inverse {y = y} f = {z : Ob} → is-equiv (λ (g : Hom y z) → g ∘ f)

  record is-equivalence {x y} (e : Hom x y) : Type (o ⊔ h) where
    no-eta-equality
    field
      linv : is-left-inverse e
      rinv : is-right-inverse e

  is-idempotent : ∀ {x} → Hom x x → Type h
  is-idempotent f = f ∘ f ＝ f

  Eqv : Ob → Ob → Type (o ⊔ h)
  Eqv x y = Σ f ∶ Hom x y , is-equivalence f

  record has-identity (x : Ob) : Type (o ⊔ h) where
    field
      idn : Hom x x
      is-idpt : is-idempotent idn
      is-eqv : is-equivalence idn
