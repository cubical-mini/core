{-# OPTIONS --safe #-}
module Notation.Pull where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  k {ℓ-obᶠ ℓ-obᵍ} {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  {ℓ-het : ℓ-sig 3 (m , k , k , _)}
  (α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-het ls))
  ⦃ _ : Refl C ⦄ where
  private module α {ls} t = Quiver-onω (α {ls} t)

  record Pull : Typeω where
    no-eta-equality
    field
      pull : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → G y lfs → F x lfs
      pull-refl : ∀{ls lfs} {y : Ob ls} {v : G y lfs} → α.Het y (pull refl v) v

    infixr 300 _◁_
    _◁_ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} → Hom x y → G y lfs → F x lfs
    p ◁ α = pull p α

open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p u = pull p u #-}
{-# DISPLAY Pull.pull-refl _ = pull-refl #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom)
  k {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  (α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)) where
  HPull  = Pull C k α


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ ⦃ _ : HPull C k α ⦄ where

  infixr 400 _>$<_
  _>$<_ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} → Hom x y → F y lfs → F x lfs
  _>$<_ f my = pull f my

  infixl 400 _>&<_
  _>&<_ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} → F y lfs → Hom x y → F x lfs
  _>&<_ my f = pull f my
