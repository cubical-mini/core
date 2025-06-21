{-# OPTIONS --safe #-}
module Notation.Lens.Bivariant.Lawful where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Bivariant.Base
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → Levels n → ℓ-sig² m}
  (F : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} → Hom x y → Quiverω m (ℓ-obᶠ lxs lys) (ℓ-homᶠ lxs lys))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Extendω C F ⦄
  where
  private module F {lxs} {lys} x y p = Quiverω (F {lxs} {lys} {x} {y} p)

  record Lawful-Extend (ls : Levels n) (lsᶠ : Levels m) : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls ls lsᶠ ⊔ ℓ-homᶠ ls ls lsᶠ lsᶠ) where
    no-eta-equality
    field
      extend-refl : {x : Ob ls} {u : F.Ob x x refl lsᶠ} → F.Hom x x refl (extend-l refl u) (extend-r refl u)
      extend-coh  : {x : Ob ls} {u : F.Ob x x refl lsᶠ} → F.Hom x x refl u (extend-r refl u)

  Lawful-Extendω : Typeω
  Lawful-Extendω = ∀{ls lsᶠ} → Lawful-Extend ls lsᶠ

open Lawful-Extend ⦃ ... ⦄ public
{-# DISPLAY Lawful-Extend.extend-refl _ = extend-refl #-}
{-# DISPLAY Lawful-Extend.extend-coh _ = extend-coh #-}
