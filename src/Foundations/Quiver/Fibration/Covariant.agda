{-# OPTIONS --safe #-}
module Foundations.Quiver.Fibration.Covariant where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : Quiver-onωᵈ C m′ Ob[_]⁻ m′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  record is-covariant-fibration : Typeω where
    no-eta-equality
    field
      lift⁺ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (u : Ob[ x ]⁻ lfs)
            → is-contr⁺ (Σₜ (Ob[ y ]⁺ lfs) (λ v → Het[ p ] u v))

open is-covariant-fibration ⦃ ... ⦄ public
{-# DISPLAY is-covariant-fibration.lift⁺ _ p u = lift⁺ p u #-}
