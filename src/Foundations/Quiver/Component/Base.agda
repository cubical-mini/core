{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Base where

open import Foundations.Quiver.Base

open import Notation.Refl

-- displayed quiver over a reflexive quiver begets a family of _small_ quivers
module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m ℓ-obᵈ ℓ-homᵈ} (D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D)
  ⦃ _ : Reflω C ⦄ where

  module _ {ls} (t : Ob ls) lsᵈ where
    Component : Quiverω 0 (λ _ → ℓ-obᵈ ls lsᵈ) (λ _ _ → ℓ-homᵈ ls ls lsᵈ lsᵈ)
    Component .Quiverω.Ob _ = Ob[ t ] lsᵈ
    Component .has-quiver-onω .Quiver-onω.Hom = Hom[ refl ]
