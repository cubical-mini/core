{-# OPTIONS --safe #-}
module Foundations.Lens.Extend.Base where

open import Foundations.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  k {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  (α : ∀{lxs lys} (x : Ob lxs) (y : Ob lys) (p : Hom x y) → HQuiver-onω k (F p) (ℓ-homᶠ lxs lys))
  ⦃ _ : Refl C ⦄ where
  private module α {lxs} {lys} x y p = Quiver-onω (α {lxs} {lys} x y p) renaming (Het to Hom)

  record Extend : Typeω where
    no-eta-equality
    field
      extend-l : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys}
                 (p : Hom x y) → (u : F (refl {x = x}) lfs) → F p lfs
      extend-r : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys}
                 (p : Hom x y) (u : F (refl {x = y}) lfs) → F p lfs
      extend-refl : ∀{ls lfs} {x : Ob ls} {u : F (refl {x = x}) lfs}
                  → α.Hom x x refl (extend-l refl u) (extend-r refl u)
      extend-coh : ∀{ls lfs} {x : Ob ls} {u : F (refl {x = x}) lfs}
                 → α.Hom x x refl u (extend-r refl u)

open Extend ⦃ ... ⦄ public
{-# DISPLAY Extend.extend-l _ p u = extend-l p u #-}
{-# DISPLAY Extend.extend-r _ p v = extend-r p v #-}
{-# DISPLAY Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Extend.extend-coh _ = extend-coh #-}
