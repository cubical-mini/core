module Foundations.Total.Instances where

open import Foundations.Base
open import Foundations.Total.Base

open import Notation.Refl
open import Notation.Underlying

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Σ̫-Refl : ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄ → Refl (Σ̫ C D)
  Σ̫-Refl .refl .fst = refl
  Σ̫-Refl .refl .snd = reflᵈ

{-# INCOHERENT Σ̫-Refl #-}


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het}
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} {D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ}
  ⦃ _ : Underlying C ⦄ where instance

  Σ̫-Underlying : Underlying Σ̫[ D ]
  Σ̫-Underlying = mk-underlying (λ x → ⌞ x .fst ⌟⁻) (λ y → ⌞ y .fst ⌟⁺) (λ f → ⌞ f .fst ⌟₁)
