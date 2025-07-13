{-# OPTIONS --safe #-}
module Notation.Lens.Extend where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  n
  {ℓ-obᶠ : Levels m → Levels m → ℓ-sig n}
  (Hom[_] : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ where

  record Extend lxs lys lfs : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-obᶠ lxs lxs lfs
    ⊔ ℓ-obᶠ lxs lys lfs ⊔ ℓ-obᶠ lys lys lfs) where
    no-eta-equality
    field
      extend-l : {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : Hom[ refl {x = x} ] lfs) → Hom[ p ] lfs
      extend-r : {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : Hom[ refl {x = y} ] lfs) → Hom[ p ] lfs

  Extendω : Typeω
  Extendω = ∀{lxs lys lfs} → Extend lxs lys lfs

open Extend ⦃ ... ⦄ public
{-# DISPLAY Extend.extend-l _ p u = extend-l p u #-}
{-# DISPLAY Extend.extend-r _ p v = extend-r p v #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {n}
  {ℓ-obᶠ : Levels m → Levels m → ℓ-sig n} {ℓ-homᶠ : Levels m → Levels m → ℓ-sig² n n}
  {Hom[_] : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → ob-sig (ℓ-obᶠ lxs lys)}
  (F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (p : Hom x y) → HQuiver-onω n Hom[ p ] (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C n Hom[_] ⦄ where
  private module F {lxs} {lys} x y p = Quiver-onω (F {lxs} {lys} {x} {y} p)

  record Lawful-Extend ls lfs : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls ls lfs ⊔ ℓ-homᶠ ls ls lfs lfs) where
    no-eta-equality
    field
      extend-refl : {x : Ob ls} {u : Hom[ refl {x = x} ] lfs} → F.Het x x refl (extend-r refl u) (extend-l refl u)
      extend-coh  : {x : Ob ls} {u : Hom[ refl {x = x} ] lfs} → F.Het x x refl (extend-r refl u) u

  Lawful-Extendω : Typeω
  Lawful-Extendω = ∀{ls lfs} → Lawful-Extend ls lfs

open Lawful-Extend ⦃ ... ⦄ public
{-# DISPLAY Lawful-Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Lawful-Extend.extend-coh _ = extend-coh #-}
