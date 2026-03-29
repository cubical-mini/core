module Foundations.Wide.Instances where

open import Foundations.Base
open import Foundations.Total.Instances
open import Foundations.Wide.Base

open import Notation.Refl
open import Notation.Underlying

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} ℓ-hom {C : HQuiver-onω m Ob ℓ-hom}
  {ℓ-homᵈ} {D : HQuiver-onωᵈ C 0 (λ _ _ → ⊤ₜ) ℓ-homᵈ} where instance

  Wide-Refl : ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄ → Refl (Wide D)
  Wide-Refl .refl .fst = refl
  Wide-Refl .refl .snd = reflᵈ

{-# INCOHERENT Wide-Refl #-}


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {ℓ-homᵈ} {D : Quiver-onωᵈ C 0 (λ _ _ → ⊤ₜ) 0 (λ _ _ → ⊤ₜ) ℓ-homᵈ}
  ⦃ u : Underlying C ⦄ where instance

  Wide-Underlying : Underlying (Wide D)
  Wide-Underlying = mk-underlying (u .Underlying.⌞_⌟⁻) (u .Underlying.⌞_⌟⁺) (λ f → u .Underlying.⌞_⌟₁ (f .fst))
  {-# INCOHERENT Wide-Underlying #-}
