{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull.Universal.Pullback where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base
open import Foundations.Quiver.Lens.Pull.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ (hp : Pull C k α) where
  private module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
  private instance _ = hp

  record Pullbacks : Typeω where
    no-eta-equality
    field
      pull-univ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} (p : Hom x y) (v : F y lfs)
                → is-prop (Fan⁻ (α x) (p ◁ v) lfs)


open Pullbacks ⦃ ... ⦄ public
  using (pull-univ)
{-# DISPLAY Pullbacks.pull-univ _ p v = pull-univ p v #-}
