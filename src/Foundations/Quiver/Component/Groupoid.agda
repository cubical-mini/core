{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component.Base

open import Notation.Refl

module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m ℓ-obᵈ ℓ-homᵈ} {D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ} (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ where instance

  Component-Refl : ∀{ls} {t : Ob ls} {lsᵈ} → Reflω (Component D t lsᵈ) -- canonical way
  Component-Refl .refl = reflᵈ _
  {-# INCOHERENT Component-Refl #-} -- TODO is it really necessary?

  -- TODO Component-Sym, Component-Comp
