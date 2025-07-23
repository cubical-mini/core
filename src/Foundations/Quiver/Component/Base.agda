{-# OPTIONS --safe #-}
module Foundations.Quiver.Component.Base where

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : SQuiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  ⦃ _ : Refl C ⦄ where

  module _ {ls} (t : Ob ls) where
    Component : Quiver-onω m′ Ob[ t ]⁻ n′ Ob[ t ]⁺ _
    Component .Quiver-onω.Het = Het[ refl ]
