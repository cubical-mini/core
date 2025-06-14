{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Bivariant.Base   public
open import Notation.Lens.Bivariant.Lawful public
open import Notation.Refl.Base

module _ {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {ℓ-obᶠ : ℓ-sig³} {ℓ-homᶠ : ℓ-sig⁴}
  {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
  (F : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (p : Hom x y) → Quiverω (ℓ-obᶠ ℓx ℓy) (ℓ-homᶠ ℓx ℓy)) where
  private module F {ℓx} {ℓy} x y p = Quiverω (F {ℓx} {ℓy} {x} {y} p)

  Disp± : ⦃ _ : Extendω C F ⦄ → Quiverωᵈ C (λ ℓ → ℓ-obᶠ ℓ ℓ ℓ) (λ ℓx ℓy → ℓ-homᶠ ℓx ℓy ℓx ℓy)
  Disp± .Quiverωᵈ.Ob[_] {ℓ} t = F.Ob t t refl ℓ
  Disp± .Quiverωᵈ.Hom[_] {x} {y} p u v = F.Hom x y p (extend-l p u) (extend-r p v)
