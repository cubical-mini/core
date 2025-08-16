{-# OPTIONS --safe #-}
module Foundations.Lens.Push.Forward where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Lens.Push.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ (hp : Push C k α)
  ⦃ _ : ∀ {ls} {t : Ob ls} → Refl (α t) ⦄ where
  private module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
  private instance _ = hp

  record UPush : Typeω where
    no-eta-equality
    field
      push-univ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : F x lfs)
                → is-central {A = Fan⁺ (α y) (u ▷ p) lfs} (u ▷ p , refl)

open UPush ⦃ ... ⦄ public
  using (push-univ)
{-# DISPLAY UPush.push-univ _ p u = push-univ p u #-}
