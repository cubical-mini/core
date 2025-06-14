{-# OPTIONS --safe #-}
module Notation.Lens.Covariant.Lawful where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Covariant.Base
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Reflω C ⦄
  (F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)) ⦃ _ : Pushω C F ⦄ where
  private module F {ℓ} x = Quiverω (F {ℓ} x)

  record Lawful-Push ℓ : Typeω where
    no-eta-equality
    field push-refl : {x : Ob ℓ} {u : F.Ob x ℓ} → F.Hom x (push refl u) u

  Lawful-Pushω : Typeω
  Lawful-Pushω = ∀{ℓ} → Lawful-Push ℓ

open Lawful-Push ⦃ ... ⦄ public
{-# DISPLAY Lawful-Push.push-refl _ = push-refl #-}
