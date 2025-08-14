{-# OPTIONS --safe #-}
module Foundations.Diagram.Exponential where

open import Foundations.Cubical.HLevel.Base
open import Foundations.Base
open import Foundations.Diagram.Product.Binary
open import Foundations.Discrete.Base
open import Foundations.Lens.Pull

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ ⦃ hp : ∀{lys} {y : Ob lys} → Pull C 0 (λ x → Disc (Hom x y)) ⦄
  {ℓ-×} ⦃ _ : Binary-products C C ℓ-× ⦄ where

  record Exponential {lxs lys les} (X : Ob lxs) (Y : Ob lys) (Y^X : Ob les) : Typeω where
    no-eta-equality
    field
      ev : Hom (Y^X × X) Y
      ƛ  : ∀{lgs} {Γ : Ob lgs} → Hom (Γ × X) Y → Hom Γ Y^X
      ƛ-commutes : ∀{lgs} {Γ : Ob lgs} (m : Hom (Γ × X) Y) → (ƛ m ×→ refl) ◁ ev ＝ m
      ƛ-unique   : ∀{lgs} {Γ : Ob lgs} (m : Hom (Γ × X) Y)
                 → is-central⁻ (Σₜ (Hom Γ Y^X) λ m′ →  (m′ ×→ refl) ◁ ev ＝ m) (ƛ m , ƛ-commutes m)

  record Cartesian-closed (ℓ-⇒ : Levels m → Levels m → Levels m) : Typeω where
    no-eta-equality
    infixr 10 _⇒_
    field
      _⇒_ : ∀{lxs lys} (X : Ob lxs) (Y : Ob lys) → Ob (ℓ-⇒ lxs lys)
      has-exponential : ∀{lxs lys} {X : Ob lxs} {Y : Ob lys} → Exponential X Y (X ⇒ Y)

  open Exponential ⦃ ... ⦄ public
  open Cartesian-closed ⦃ ... ⦄ public
    using (_⇒_)

{-# DISPLAY Exponential.ev _ = ev #-}
{-# DISPLAY Exponential.ƛ _ f = ƛ f #-}
{-# DISPLAY Exponential.ƛ-commutes _ m = ƛ-commutes m #-}
{-# DISPLAY Exponential.ƛ-unique _ m = ƛ-commutes m #-}
{-# DISPLAY Cartesian-closed._⇒_ _ X Y = X ⇒ Y #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  ⦃ _ : Refl C ⦄ ⦃ hp : ∀{lys} {y : Ob lys} → Pull C 0 (λ x → Disc (Hom x y)) ⦄
  {ℓ-×} ⦃ _ : Binary-products C C ℓ-× ⦄ where instance

  Cartesian-closed→Exponential : ∀ {ℓ-⇒ lxs lys} ⦃ cc : Cartesian-closed C ℓ-⇒ ⦄
                                 {X : Ob lxs} {Y : Ob lys}
                               → Exponential C X Y (X ⇒ Y)
  Cartesian-closed→Exponential ⦃ cc ⦄ = cc .Cartesian-closed.has-exponential
  {-# OVERLAPPABLE Cartesian-closed→Exponential #-}
