{-# OPTIONS --safe #-}
module Foundations.Quiver.Fibration.Contravariant where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻} {ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : Quiver-onωᵈ C m′ Ob[_]⁻ m′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  record is-contravariant-fibration : Typeω where
    no-eta-equality
    field
      lift-ob⁻ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (v : Ob[ y ]⁺ lfs)
               → Ob[ x ]⁻ lfs
      lift-het⁻ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (v : Ob[ y ]⁺ lfs)
                → Het[ p ] (lift-ob⁻ p v) v
      lift-unique⁻ : ∀{lxs lys lfs} {x : Ob⁻ lxs} {y : Ob⁺ lys} (p : Het x y) (v : Ob[ y ]⁺ lfs)
                   → is-central⁻ (Σₜ (Ob[ x ]⁻ lfs) (λ u → Het[ p ] u v)) (lift-ob⁻ p v , lift-het⁻ p v)

open is-contravariant-fibration ⦃ ... ⦄ public
{-# DISPLAY is-contravariant-fibration.lift-ob⁻ _ p v = lift-ob⁻ p v #-}
{-# DISPLAY is-contravariant-fibration.lift-het⁻ _ p v = lift-het⁻ p v #-}
{-# DISPLAY is-contravariant-fibration.lift-unique⁻ _ p v = lift-unique⁻ p v #-}
