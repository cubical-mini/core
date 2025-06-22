{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Base where

open import Foundations.Quiver.Base

open import Notation.Refl

-- displayed quiver over a reflexive quiver begets a family of _small_ quivers
module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m : ℕ} {ℓ-obᵈ : Levels n → ℓ-sig m} {ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m}
  (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄ where

  module _ {ls : Levels n} (t : Ob ls) (lsᵈ : Levels m) where
    Component : Quiverω 0 (λ _ → ℓ-obᵈ ls lsᵈ) (λ _ _ → ℓ-homᵈ ls ls lsᵈ lsᵈ)
    Component .Quiverω.Ob _ = Ob[ t ] lsᵈ
    Component .Quiverω.Hom = Hom[ refl ]
