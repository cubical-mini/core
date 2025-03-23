```agda

{-# OPTIONS --safe #-}

module Lib.Path.Homotopy where

open import Prim.Base
open import Prim.Pi

open import Lib.Path.Base

infix 2 _∼_

_∼_ :  ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → ((x : A) → B x) → ((x : A) → B x) → Type (ℓ ⊔ ℓ')
f ∼ g = ∀ x → f x ≡ g x

-- happly is an on-the-nose inverse to funext
happly : ∀ {a b} {A : Type a} {B : A → Type b} {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x

```

Homotopies are an equivalence relation

```

module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} where
  refl-htpy : (f : (x : A) → B x) → f ∼ f
  refl-htpy f x i = f x

  sym-htpy : {f g : (x : A) → B x} → f ∼ g → g ∼ f
  sym-htpy H x i = H x (~ i)

  concat-htpy : {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
  concat-htpy {f} {g} {h} H K x = H x ∙ K x

```

We also have the type of homotopies over homotopies

```

module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} where
  _≈_ : {f g : (x : A) → B x} → f ∼ g → f ∼ g → Type (ℓ ⊔ ℓ')
  H ≈ K = (x : A) → H x ≡ K x

```

Predicate definitions for homotopies we are often concerned with

```

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  left-inverse : (B → A) → (A → B) → Type ℓ
  left-inverse g f = (x : A) → g (f x) ≡ x --

  right-inverse : (B → A) → (A → B) → Type ℓ'
  right-inverse g f = (x : B) → f (g x) ≡ x


-- As defined in Rijke's Intro to HoTT
comm-triangle : ∀ {u v w} {A : Type u} {B : A → Type v} {X : Type w}
              → ((x : A) → B x) → ({x : A} → B x → X) → (A → X) → Type (u ⊔ w)
comm-triangle f g h = h ∼ g ∘ f

comm-square : ∀ {u u' v v'}
            → {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
            → (A → A') → (A → B) → (A' → B') → (B → B') → Type (u ⊔ v')
comm-square g f f' h = h ∘ f ∼ f' ∘ g
