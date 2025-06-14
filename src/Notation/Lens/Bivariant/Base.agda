{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {ℓ-obᶠ : ℓ-sig³} {ℓ-homᶠ : ℓ-sig⁴}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Reflω C ⦄
  (F : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Quiverω (ℓ-obᶠ ℓx ℓy) (ℓ-homᶠ ℓx ℓy)) where
  private module F {ℓx} {ℓy} x y p = Quiverω (F {ℓx} {ℓy} {x} {y} p)

  record Extend ℓx ℓy : Type (ℓ-ob ℓx ⊔ ℓ-ob ℓy ⊔ ℓ-hom ℓx ℓy ⊔ ℓ-obᶠ ℓx ℓx ℓx ⊔ ℓ-obᶠ ℓy ℓy ℓy ⊔ ℓ-obᶠ ℓx ℓy ℓx ⊔ ℓ-obᶠ ℓx ℓy ℓy) where
    no-eta-equality
    field
      extend-l : {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) (u : F.Ob x x refl ℓx) → F.Ob x y p ℓx
      extend-r : {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) (v : F.Ob y y refl ℓy) → F.Ob x y p ℓy

  Extendω : Typeω
  Extendω = ∀{ℓx ℓy} → Extend ℓx ℓy

open Extend ⦃ ... ⦄ public
{-# DISPLAY Extend.extend-l _ p u = extend-l p u #-}
{-# DISPLAY Extend.extend-r _ p v = extend-l p v #-}
