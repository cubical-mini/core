{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant.Lawful where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Bivariant.Base
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {ℓ-obᶠ : ℓ-sig³} {ℓ-homᶠ : ℓ-sig⁴}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Reflω C ⦄
  (F : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Quiverω (ℓ-obᶠ ℓx ℓy) (ℓ-homᶠ ℓx ℓy))
  ⦃ _ : Extendω C F ⦄ where
  private module F {ℓx} {ℓy} x y p = Quiverω (F {ℓx} {ℓy} {x} {y} p)

  record Lawful-Extend ℓ : Type (ℓ-ob ℓ ⊔ ℓ-obᶠ ℓ ℓ ℓ ⊔ ℓ-homᶠ ℓ ℓ ℓ ℓ) where
    no-eta-equality
    field
      extend-refl : {x : Ob ℓ} {u : F.Ob x x refl ℓ} → F.Hom x x refl (extend-l refl u) (extend-r refl u)
      extend-coh  : {x : Ob ℓ} {u : F.Ob x x refl ℓ} → F.Hom x x refl u (extend-r refl u)

  Lawful-Extendω : Typeω
  Lawful-Extendω = ∀{ℓ} → Lawful-Extend ℓ

open Lawful-Extend ⦃ ... ⦄ public
{-# DISPLAY Lawful-Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Lawful-Extend.extend-coh _ = extend-coh #-}
