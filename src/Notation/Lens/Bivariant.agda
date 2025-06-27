{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ where
  private module F {lxs} {lys} x y p = Quiverω (F {lxs} {lys} {x} {y} p)

  record Extend lxs lys lsᶠ : Type
    ( ℓ-ob lxs ⊔ ℓ-hom lxs lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lys lys ⊔ ℓ-hom lxs lys
    ⊔ ℓ-obᶠ lxs lxs lsᶠ ⊔ ℓ-obᶠ lxs lys lsᶠ ⊔ ℓ-obᶠ lys lys lsᶠ) where
    no-eta-equality
    field
      extend-l : {x : Ob lxs} {y : Ob lys} (p : Hom x y) (u : F.Ob x x refl lsᶠ) → F.Ob x y p lsᶠ
      extend-r : {x : Ob lxs} {y : Ob lys} (p : Hom x y) (v : F.Ob y y refl lsᶠ) → F.Ob x y p lsᶠ

  Extendω : Typeω
  Extendω = ∀{lxs lys lsᶠ} → Extend lxs lys lsᶠ

open Extend ⦃ ... ⦄ public
{-# DISPLAY Extend.extend-l _ p u = extend-l p u #-}
{-# DISPLAY Extend.extend-r _ p v = extend-r p v #-}


module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C F ⦄ where
  private module F {lxs} {lys} x y p = Quiverω (F {lxs} {lys} {x} {y} p)

  record Lawful-Extend ls lsᶠ : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls ls lsᶠ ⊔ ℓ-homᶠ ls ls lsᶠ lsᶠ) where
    no-eta-equality
    field
      extend-refl : {x : Ob ls} {u : F.Ob x x refl lsᶠ} → F.Hom x x refl (extend-l refl u) (extend-r refl u)
      extend-coh  : {x : Ob ls} {u : F.Ob x x refl lsᶠ} → F.Hom x x refl u (extend-r refl u)

  Lawful-Extendω : Typeω
  Lawful-Extendω = ∀{ls lsᶠ} → Lawful-Extend ls lsᶠ

open Lawful-Extend ⦃ ... ⦄ public
{-# DISPLAY Lawful-Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Lawful-Extend.extend-coh _ = extend-coh #-}
