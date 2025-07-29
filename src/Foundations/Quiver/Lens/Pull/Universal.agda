{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull.Universal where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base
open import Foundations.Quiver.Lens.Pull.Base

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  (α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)) where
  private module α {ls} t = Quiver-onω (α {ls} t)

  record Pullbacks : Typeω where
    no-eta-equality
    field
      ⦃ hp ⦄    : HPull C k α
      pull-univ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} (p : Hom x y) (v : F y lfs)
                → is-prop (Fan⁻ (α x) (p ◁ v) lfs)

open Pullbacks ⦃ ... ⦄ public
  using (pull-univ)
{-# DISPLAY Pullbacks.pull-univ _ p v = pull-univ p v #-}
