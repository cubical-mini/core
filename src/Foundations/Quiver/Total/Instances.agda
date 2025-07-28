{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Instances where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base

open import Notation.Refl
open import Notation.Underlying

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Σ-Refl : ⦃ rd : Reflᵈ D ⦄ → Refl (Σ C D)
  Σ-Refl ⦃ rd ⦄ .refl .fst = rd .Reflᵈ.rfl .refl
  Σ-Refl .refl .snd = reflᵈ

{-# INCOHERENT Σ-Refl #-}


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het}
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} {D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ}
  ⦃ _ : Underlying C ⦄ where instance

  Σ-Underlying : Underlying Σ[ D ]
  Σ-Underlying = mk-underlying (λ x → ⌞ x .fst ⌟⁻) (λ y → ⌞ y .fst ⌟⁺) (λ f → ⌞ f .fst ⌟₁)
