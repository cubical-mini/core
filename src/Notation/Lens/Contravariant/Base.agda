{-# OPTIONS --safe #-}
module Notation.Lens.Contravariant.Base where

open import Prim.Type

open import Notation.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᶠ : Levels n → ℓ-sig m} {ℓ-homᶠ : Levels n → ℓ-sig² m}
  (F : {ls : Levels n} → Ob ls → Quiverω m (ℓ-obᶠ ls) (ℓ-homᶠ ls))
  where
  private module F {ls} x = Quiverω (F {ls} x)

  record Pull (lxs lys : Levels n) (lsᶠ : Levels m) : Type
    ( ℓ-ob lxs ⊔ ℓ-ob lys ⊔ ℓ-hom lxs lys
    ⊔ ℓ-obᶠ lxs lsᶠ ⊔ ℓ-obᶠ lys lsᶠ) where
    no-eta-equality
    field pull : {x : Ob lxs} {y : Ob lys} (p : Hom x y) → F.Ob y lsᶠ → F.Ob x lsᶠ

  Pullω : Typeω
  Pullω = ∀{lxs lys lsᶠ} → Pull lxs lys lsᶠ

open Pull ⦃ ... ⦄ public
{-# DISPLAY Pull.pull _ p u = pull p u #-}
