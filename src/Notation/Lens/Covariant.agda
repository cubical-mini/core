{-# OPTIONS --safe #-}
module Notation.Lens.Covariant where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Covariant.Base   public
open import Notation.Lens.Covariant.Lawful public
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)) ⦃ _ : Pushω C F ⦄ where
  private module F {ℓ} x = Quiverω (F {ℓ} x)

  Disp⁺ : Quiverωᵈ C (λ ℓ → ℓ-obᶠ ℓ ℓ) (λ _ ℓy → ℓ-homᶠ ℓy ℓy ℓy)
  Disp⁺ .Quiverωᵈ.Ob[_] {ℓ} x = F.Ob x ℓ
  Disp⁺ .Quiverωᵈ.Hom[_] {y} p u v = F.Hom y (push p u) v
