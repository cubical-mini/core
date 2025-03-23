{-# OPTIONS --safe #-}
module Control.Diagram.Exponential where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Diagram.Product.Binary
open import Control.Diagram.Terminal
open import Control.Reflexivity
open import Control.Structures.Quiver

module _ (C : Quiver) ⦃ _ : Refl C ⦄ ⦃ _ : Comp C ⦄ ⦃ _ : Binary-products C ⦄ where
  open Quiver C

  record is-exponential ℓg {u v ℓe} {A : Ob u} {B : Ob v}
    (B^A : Ob ℓe) (ev : Hom (B^A × A) B) : Type (ob-lvl ℓg ⊔ hom-lvl ℓg ℓe ⊔ hom-lvl (ℓg ⊔ u) v) where
    no-eta-equality
    field
      ƛ        : {Γ : Ob ℓg} → Hom (Γ × A) B → Hom Γ B^A
      commutes : {Γ : Ob ℓg} (m : Hom (Γ × A) B) → ev ∘ (ƛ m ×→ refl) ≡ m
      unique   : {Γ : Ob ℓg} {m : Hom (Γ × A) B} (m′ : Hom Γ B^A)
               → ev ∘ (m′ ×→ refl) ≡ m → m′ ≡ ƛ m

  record Exponential {u v} (A : Ob u) (B : Ob v) (B^A : Ob (u ⊔ v)) : Typeω where
    no-eta-equality
    field
      ev : Hom (B^A × A) B
      has-is-exp : {ℓg : Level} → is-exponential ℓg B^A ev

  record Cartesian-closed : Typeω where
    no-eta-equality
    infixr 50 _⇒_
    field
      _⇒_ : ∀ {u v} (A : Ob u) (B : Ob v) → Ob (u ⊔ v)
      has-exp : ∀ {u v} {A : Ob u} {B : Ob v} → Exponential A B (A ⇒ B)

open is-exponential ⦃ ... ⦄ public
  renaming (commutes to ƛ-commutes; unique to ƛ-unique)
open Exponential ⦃ ... ⦄ public
  using (ev)
open Cartesian-closed ⦃ ... ⦄ public
  using (_⇒_)

{-# DISPLAY is-exponential.ƛ _ f = ƛ f #-}
{-# DISPLAY is-exponential.commutes _ f = ƛ-commutes f #-}
{-# DISPLAY is-exponential.unique _ f p = ƛ-unique f p #-}
{-# DISPLAY Exponential.ev _ = ev #-}
{-# DISPLAY Cartesian-closed._⇒_ _ A B = A ⇒ B #-}

module _
  {C : Quiver} (let open Quiver C) ⦃ _ : Refl C ⦄ ⦃ _ : Comp C ⦄ ⦃ _ : Binary-products C ⦄
  ∀ {u v} {A : Ob u} {B : Ob v} where instance
    is-exp-helper : {ℓg : Level} {E : Ob (u ⊔ v)} ⦃ e : Exponential C A B E ⦄ → is-exponential C ℓg E ev
    is-exp-helper ⦃ e ⦄ = e .Exponential.has-is-exp

    exp-helper : ⦃ e : Cartesian-closed C ⦄ → Exponential C A B (A ⇒ B)
    exp-helper ⦃ e ⦄ = e .Cartesian-closed.has-exp
