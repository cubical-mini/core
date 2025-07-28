{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Push.Universal where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base
open import Foundations.Quiver.Lens.Push.Base

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  (α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)) where
  private module α {ls} t = Quiver-onω (α {ls} t)

  record Pushforwards : Typeω where
    no-eta-equality
    field
      ⦃ hp ⦄    : HPush C k α
      push-univ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : F x lfs)
                → is-prop (Fan⁺ (α y) (u ▷ p) lfs)

open Pushforwards ⦃ ... ⦄ public
  using (push-univ)
{-# DISPLAY Pushforwards.push-univ _ p u = push-univ p u #-}
