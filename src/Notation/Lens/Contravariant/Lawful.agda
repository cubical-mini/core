{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant.Lawful where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Contravariant.Base
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  (F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pullω C F ⦄
  where
  private module F {ls} x = Quiverω (F {ls} x)

  record Lawful-Pull (ls : Levels n) (lsᶠ : Levels m) : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls lsᶠ ⊔ ℓ-homᶠ ls lsᶠ lsᶠ) where
    no-eta-equality
    field pull-refl : {y : Ob ls} {v : F.Ob y lsᶠ} → F.Hom y v (pull refl v)

  Lawful-Pullω : Typeω
  Lawful-Pullω = ∀{ls lsᶠ} → Lawful-Pull ls lsᶠ

open Lawful-Pull ⦃ ... ⦄ public
  using (pull-refl)
{-# DISPLAY Lawful-Pull.pull-refl _ = pull-refl #-}
