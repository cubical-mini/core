{-# OPTIONS --safe #-}
module Quiver.Lens.Bivariant where

open import Prim.Type

open import Quiver.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ ℓ-homᶠ : ℓ-sig²} (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C)
  (F : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Quiverω (λ _ → ℓ-obᶠ ℓx ℓy) (λ _ _ → ℓ-homᶠ ℓx ℓy)) where
  private module F {ℓx} {ℓy} x y p = Quiverω (F {ℓx} {ℓy} {x} {y} p)
  record Extend : Typeω where
    no-eta-equality
    field
      extend-l    : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) (u : F.Ob x x refl ℓx) → F.Ob x y p ℓx
      extend-r    : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) (v : F.Ob y y refl ℓy) → F.Ob x y p ℓy
      extend-refl : ∀{ℓ} {x : Ob ℓ} {u : F.Ob x x refl ℓ} → F.Hom x x refl (extend-l refl u) (extend-r refl u)
      extend-coh  : ∀{ℓ} {x : Ob ℓ} {u : F.Ob x x refl ℓ} → F.Hom x x refl u (extend-r refl u)
open Extend ⦃ ... ⦄ public
{-# DISPLAY Extend.extend-l _ p u = extend-l p u #-}
{-# DISPLAY Extend.extend-r _ p v = extend-l p v #-}
{-# DISPLAY Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Extend.extend-coh _ = extend-coh #-}

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ ℓ-homᶠ : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (F : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Quiverω (λ _ → ℓ-obᶠ ℓx ℓy) (λ _ _ → ℓ-homᶠ ℓx ℓy)) where
  private module F {ℓx} {ℓy} x y p = Quiverω (F {ℓx} {ℓy} {x} {y} p)

  open Quiverωᵈ
  Disp± : ⦃ _ : Extend C F ⦄ → Quiverωᵈ C (λ ℓ → ℓ-obᶠ ℓ ℓ) ℓ-homᶠ
  Disp± .Ob[_] {ℓ} t = F.Ob t t refl ℓ
  Disp± .Hom[_] {x} {y} p u v = F.Hom x y p (extend-l p u) (extend-r p v)
  Disp± .reflᵈ = extend-refl
