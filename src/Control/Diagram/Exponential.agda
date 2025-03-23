{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Exponential where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Diagram.Product.Binary
open import Foundations.Cat.Diagram.Terminal
open import Foundations.Cat.Reflexivity
open import Foundations.Cat.Structures.Quiver

module _ (C : Quiver) ⦃ _ : Refl C ⦄ ⦃ _ : Comp C ⦄ ⦃ _ : Binary-products C ⦄ where
  open Quiver C

  record is-exponential ℓg {ℓa ℓb ℓe} {A : Ob ℓa} {B : Ob ℓb}
    (B^A : Ob ℓe) (ev : Hom (B^A × A) B) : Type (ob-lvl ℓg l⊔ hom-lvl ℓg ℓe l⊔ hom-lvl (ℓg l⊔ ℓa) ℓb) where
    no-eta-equality
    field
      ƛ        : {Γ : Ob ℓg} → Hom (Γ × A) B → Hom Γ B^A
      commutes : {Γ : Ob ℓg} (m : Hom (Γ × A) B) → ev ∘ (ƛ m ×→ refl) ＝ m
      unique   : {Γ : Ob ℓg} {m : Hom (Γ × A) B} (m′ : Hom Γ B^A)
               → ev ∘ (m′ ×→ refl) ＝ m → m′ ＝ ƛ m

  record Exponential {ℓa ℓb} (A : Ob ℓa) (B : Ob ℓb) (B^A : Ob (ℓa l⊔ ℓb)) : Typeω where
    no-eta-equality
    field
      ev : Hom (B^A × A) B
      has-is-exp : {ℓg : Level} → is-exponential ℓg B^A ev

  record Cartesian-closed : Typeω where
    no-eta-equality
    infixr 50 _⇒_
    field
      _⇒_ : {ℓa ℓb : Level} (A : Ob ℓa) (B : Ob ℓb) → Ob (ℓa l⊔ ℓb)
      has-exp : {ℓa ℓb : Level} {A : Ob ℓa} {B : Ob ℓb} → Exponential A B (A ⇒ B)

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
  {ℓa ℓb : Level} {A : Ob ℓa} {B : Ob ℓb} where instance
    is-exp-helper : {ℓg : Level} {E : Ob (ℓa l⊔ ℓb)} ⦃ e : Exponential C A B E ⦄ → is-exponential C ℓg E ev
    is-exp-helper ⦃ e ⦄ = e .Exponential.has-is-exp

    exp-helper : ⦃ e : Cartesian-closed C ⦄ → Exponential C A B (A ⇒ B)
    exp-helper ⦃ e ⦄ = e .Cartesian-closed.has-exp
