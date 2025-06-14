{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant.Lawful where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Contravariant.Base
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  (C : Quiverω ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Reflω C ⦄
  (F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)) ⦃ _ : Pullω C F ⦄ where
  private module F {ℓ} x = Quiverω (F {ℓ} x)

  record Lawful-Pull ℓ : Typeω where
    no-eta-equality
    field pull-refl : {x : Ob ℓ} {v : F.Ob x ℓ} → F.Hom x v (pull refl v)

  Lawful-Pullω : Typeω
  Lawful-Pullω = ∀{ℓ} → Lawful-Pull ℓ

open Lawful-Pull ⦃ ... ⦄ public
{-# DISPLAY Lawful-Pull.pull-refl _ = pull-refl #-}
