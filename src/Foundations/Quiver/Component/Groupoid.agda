{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component.Base

open import Notation.Refl

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  {D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ} (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ where instance

  Component-Refl : {ls : Levels n} {t : Ob ls} {lsᵈ : Levels m} → Reflω (Component D t lsᵈ) -- canonical way
  Component-Refl .refl = reflᵈ _
  {-# INCOHERENT Component-Refl #-} -- TODO is it really necessary?

  -- TODO Component-Sym, Component-Comp
