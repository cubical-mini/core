{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Underlying where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base

open import Notation.Underlying

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het}
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} {D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ}
  ⦃ _ : Underlying C ⦄ where instance

  Σ-Underlying : Underlying Σ[ D ]
  Σ-Underlying = mk-underlying (λ x → ⌞ x .fst ⌟⁻) (λ y → ⌞ y .fst ⌟⁺)
