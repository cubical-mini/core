{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Underlying where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Wide.Base

open import Notation.Underlying

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {ℓ-homᵈ} {D : Quiver-onωᵈ C 0 (λ _ _ → ⊤) 0 (λ _ _ → ⊤) ℓ-homᵈ}
  ⦃ u : Underlying C ⦄ where instance

  Wide-Underlying : Underlying (Wide D)
  Wide-Underlying = mk-underlying (u .Underlying.⌞_⌟⁻) (u .Underlying.⌞_⌟⁺) (λ f → u .Underlying.⌞_⌟₁ (f .fst))
  {-# INCOHERENT Wide-Underlying #-}
