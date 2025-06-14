{-# OPTIONS --safe #-}
module Notation.Lens.Covariant.Base where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C)
  (F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)) where
  private module F {ℓ} x = Quiverω (F {ℓ} x)

  record Push ℓx ℓy : Type (ℓ-ob ℓx ⊔ ℓ-ob ℓy ⊔ ℓ-hom ℓx ℓy ⊔ ℓ-obᶠ ℓx ℓx ⊔ ℓ-obᶠ ℓy ℓy) where
    no-eta-equality
    field push : {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → F.Ob x ℓx → F.Ob y ℓy

  Pushω : Typeω
  Pushω = ∀{ℓx ℓy} → Push ℓx ℓy

open Push ⦃ ... ⦄ public
{-# DISPLAY Push.push _ p u = push p u #-}
