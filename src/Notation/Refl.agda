{-# OPTIONS --safe #-}
module Notation.Refl where

open import Foundations.Quiver.Base

module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) where

  record Refl ls : Type (ℓ-ob ls ⊔ ℓ-hom ls ls) where
    no-eta-equality
    field refl : ∀{x} → Hom {lys = ls} x x

  Reflω : Typeω
  Reflω = ∀ {ls} → Refl ls

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m ℓ-obᵈ ℓ-homᵈ} (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄ where

  record Reflᵈ ls lsᵈ : Type (ℓ-obᵈ ls lsᵈ ⊔ ℓ-homᵈ ls ls lsᵈ lsᵈ ⊔ ℓ-ob ls) where
    no-eta-equality
    field reflᵈ : {x : Ob ls} (x′ : Ob[ x ] lsᵈ) → Hom[ refl ] x′ x′

  Reflωᵈ = ∀ {ls lsᵈ} → Reflᵈ ls lsᵈ

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}
