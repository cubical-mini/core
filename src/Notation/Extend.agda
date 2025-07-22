{-# OPTIONS --safe #-}
module Notation.Extend where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  k {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)}
  (F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ where

  record Extend lxs lys lfs : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-obᶠ lxs lxs lfs
    ⊔ ℓ-obᶠ lxs lys lfs ⊔ ℓ-obᶠ lys lys lfs) where
    no-eta-equality
    field
      extend-l : {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : F (refl {x = x}) lfs) → F p lfs
      extend-r : {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : F (refl {x = y}) lfs) → F p lfs

  Extendω : Typeω
  Extendω = ∀{lxs lys lfs} → Extend lxs lys lfs

open Extend ⦃ ... ⦄ public
{-# DISPLAY Extend.extend-l _ p u = extend-l p u #-}
{-# DISPLAY Extend.extend-r _ p v = extend-r p v #-}


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 3 (m , m , k , _)} {ℓ-homᶠ : ℓ-sig 4 (m , m , k , k , _)}
  {F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  (α : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω k (F p) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C k F ⦄ where
  private module α {lxs} {lys} x y p = Quiver-onω (α {lxs} {lys} {x} {y} p)

  record Lawful-Extend ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls ls lfs ⊔ ℓ-homᶠ ls ls lfs lfs) where
    no-eta-equality
    field
      extend-refl : {x : Ob ls} {u : F (refl {x = x}) lfs} → α.Het x x refl (extend-r refl u) (extend-l refl u)
      extend-coh  : {x : Ob ls} {u : F (refl {x = x}) lfs} → α.Het x x refl (extend-r refl u) u

  Lawful-Extendω : Typeω
  Lawful-Extendω = ∀{ls lfs} → Lawful-Extend ls lfs

open Lawful-Extend ⦃ ... ⦄ public
{-# DISPLAY Lawful-Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Lawful-Extend.extend-coh _ = extend-coh #-}
