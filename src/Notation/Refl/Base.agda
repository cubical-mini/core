{-# OPTIONS --safe #-}
module Notation.Refl.Base where

open import Notation.Base

module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) where

  record Refl (ls : Levels n) : Type (ℓ-ob ls ⊔ ℓ-hom ls ls) where
    no-eta-equality
    field refl : ∀{x} → Hom {lys = ls} x x

  Reflω : Typeω
  Reflω = ∀ {ls} → Refl ls

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄
  where

  record Reflᵈ (ls : Levels n) (lsᵈ : Levels m) : Type (ℓ-obᵈ ls lsᵈ ⊔ ℓ-homᵈ ls ls lsᵈ lsᵈ ⊔ ℓ-ob ls) where
    no-eta-equality
    field reflᵈ : {x : Ob ls} (x′ : Ob[ x ] lsᵈ) → Hom[ refl ] x′ x′

  Reflωᵈ = ∀ {ls lsᵈ} → Reflᵈ ls lsᵈ

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}


-- displayed quiver over a reflexive quiver begets a family of _small_ quivers
module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  where

  module _ {ls : Levels n} ⦃ _ : Refl C ls ⦄ (t : Ob ls) (lsᵈ : Levels m) where
    Component : Quiverω 0 (λ _ → ℓ-obᵈ ls lsᵈ) (λ _ _ → ℓ-homᵈ ls ls lsᵈ lsᵈ)
    Component .Quiverω.Ob _ = Ob[ t ] lsᵈ
    Component .Quiverω.Hom = Hom[ refl ]
