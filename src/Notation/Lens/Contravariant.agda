{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Contravariant.Base   public
open import Notation.Lens.Contravariant.Lawful public
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom ℓ-obᶠ : ℓ-sig²} {ℓ-homᶠ : ℓ-sig³}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C)
  (F : ∀{ℓt} (t : Ob ℓt) → Quiverω (ℓ-obᶠ ℓt) (ℓ-homᶠ ℓt)) ⦃ _ : Pullω C F ⦄ where
  private module F {ℓ} x = Quiverω (F {ℓ} x)

  Disp⁻ : Quiverωᵈ C (λ ℓ → ℓ-obᶠ ℓ ℓ) (λ ℓx _ → ℓ-homᶠ ℓx ℓx ℓx)
  Disp⁻ .Quiverωᵈ.Ob[_] {ℓ} x = F.Ob x ℓ
  Disp⁻ .Quiverωᵈ.Hom[_] {x} p u v = F.Hom x u (pull p v)
