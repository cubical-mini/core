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
      lift-ob⁺ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (u : Ob[ x ]⁻ lfs)
               → Ob[ y ]⁺ lfs
      lift-het⁺ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (u : Ob[ x ]⁻ lfs)
                → Het[ p ] u (lift-ob⁺ p u)
      lift-unique⁺ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (u : Ob[ x ]⁻ lfs)
                   → is-central⁺ (Σₜ (Ob[ y ]⁺ lfs) (λ v → Het[ p ] u v)) (lift-ob⁺ p u , lift-het⁺ p u)

open is-covariant-fibration ⦃ ... ⦄ public
{-# DISPLAY is-covariant-fibration.lift-ob⁺ _ p u = lift-ob⁺ p u #-}
{-# DISPLAY is-covariant-fibration.lift-het⁺ _ p u = lift-het⁺ p u #-}
{-# DISPLAY is-covariant-fibration.lift-unique⁺ _ p u = lift-het⁺ p u #-}
