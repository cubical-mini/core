{-# OPTIONS --safe #-}
module Notation.Lens.Covariant.Lawful where

open import Prim.Type

open import Notation.Base
open import Notation.Lens.Covariant.Base
open import Notation.Refl.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  (F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls))
  ⦃ _ : Reflω C ⦄ ⦃ _ : Pushω C F ⦄
  where
  private module F {ls} x = Quiverω (F {ls} x)

  record Lawful-Push (ls : Levels n) (lsᶠ : Levels m) : Type (ℓ-ob ls ⊔ ℓ-obᶠ ls lsᶠ ⊔ ℓ-homᶠ ls lsᶠ lsᶠ) where
    no-eta-equality
    field push-refl : {x : Ob ls} {u : F.Ob x lsᶠ} → F.Hom x (push refl u) u

  Lawful-Pushω : Typeω
  Lawful-Pushω = ∀{ls lsᶠ} → Lawful-Push ls lsᶠ

open Lawful-Push ⦃ ... ⦄ public
  using (push-refl)
{-# DISPLAY Lawful-Push.push-refl _ = push-refl #-}
