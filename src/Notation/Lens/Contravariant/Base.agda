{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant.Base where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C)
  (F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)) where
  private module F {ℓ} x = Quiverω (F {ℓ} x)

  record Pull ℓx ℓy : Type (ℓ-ob ℓx ⊔ ℓ-ob ℓy ⊔ ℓ-hom ℓx ℓy ⊔ ℓ-obᶠ ℓx ℓx ⊔ ℓ-obᶠ ℓy ℓy) where
    no-eta-equality
    field pull : {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → F.Ob y ℓy → F.Ob x ℓx

  Pullω : Typeω
  Pullω = ∀{ℓx ℓy} → Pull ℓx ℓy

open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p u = pull p u #-}
