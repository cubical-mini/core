{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄
  where
  private module F {lxs} {lys} x y p = Quiverω (F {lxs} {lys} {x} {y} p)

  record Extend (lxs lys : Levels n) (lsᶠ : Levels m) : Type
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
{-# DISPLAY Extend.extend-r _ p v = extend-l p v #-}
