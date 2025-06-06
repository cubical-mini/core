{-# OPTIONS --safe #-}
module Quiver.Lens.Contravariant where

open import Prim.Type

open import Quiver.Base

module _ {ℓ-ob ℓ-obᶠ ℓ-homᶠ : ℓ-sig¹} {ℓ-hom : ℓ-sig²} (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C)
  (F : ∀{ℓ} (t : Ob ℓ) → Quiverω (λ _ → ℓ-obᶠ ℓ) (λ _ _ → ℓ-homᶠ ℓ)) where
  private module F {ℓ} x = Quiverω (F {ℓ} x)
  record Pull : Typeω where
    no-eta-equality
    field
      pull      : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → F.Ob y ℓy → F.Ob x ℓx
      pull-refl : ∀{ℓ}{x : Ob ℓ} {v : F.Ob x ℓ} → F.Hom x v (pull refl v)
open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p v = pull p v #-}
{-# DISPLAY Pull.pull-refl _ = pull-refl #-}

module _ {ℓ-ob ℓ-obᶠ ℓ-homᶠ : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (F : ∀{ℓ} (t : Ob ℓ) → Quiverω (λ _ → ℓ-obᶠ ℓ) (λ _ _ → ℓ-homᶠ ℓ)) where
  private module F {ℓ} x = Quiverω (F {ℓ} x)
  open Quiverωᵈ
  Disp⁻ : ⦃ _ : Pull C F ⦄ → Quiverωᵈ C ℓ-obᶠ (λ ℓx _ → ℓ-homᶠ ℓx)
  Disp⁻ .Ob[_] {ℓ} x = F.Ob x ℓ
  Disp⁻ .Hom[_] {x} p u v = F.Hom x u (pull p v)
  Disp⁻ .reflᵈ = pull-refl
