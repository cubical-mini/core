{-# OPTIONS --safe #-}
module Quiver.Lens.Covariant where

open import Prim.Type

open import Quiver.Base

module _ {ℓ-ob ℓ-obᶠ ℓ-homᶠ : ℓ-sig¹} {ℓ-hom : ℓ-sig²} (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C)
  (F : ∀{ℓ} (t : Ob ℓ) → Quiverω (λ _ → ℓ-obᶠ ℓ) (λ _ _ → ℓ-homᶠ ℓ)) where
  private module F {ℓ} x = Quiverω (F {ℓ} x)
  record Push : Typeω where
    no-eta-equality
    field
      push      : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → F.Ob x ℓx → F.Ob y ℓy
      push-refl : ∀{ℓ}{x : Ob ℓ} {u : F.Ob x ℓ} → F.Hom x (push refl u) u
open Push ⦃ ... ⦄ public
{-# DISPLAY Push.push _ p u = push p u #-}
{-# DISPLAY Push.push-refl _ = push-refl #-}

module _ {ℓ-ob ℓ-obᶠ ℓ-homᶠ : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (F : ∀{ℓ} (t : Ob ℓ) → Quiverω (λ _ → ℓ-obᶠ ℓ) (λ _ _ → ℓ-homᶠ ℓ)) where
  private module F {ℓ} x = Quiverω (F {ℓ} x)
  open Quiverωᵈ
  Disp⁺ : ⦃ _ : Push C F ⦄ → Quiverωᵈ C ℓ-obᶠ (λ _ ℓy → ℓ-homᶠ ℓy)
  Disp⁺ .Ob[_] {ℓ} x = F.Ob x ℓ
  Disp⁺ .Hom[_] {y} p u v = F.Hom y (push p u) v
  Disp⁺ .reflᵈ = push-refl
