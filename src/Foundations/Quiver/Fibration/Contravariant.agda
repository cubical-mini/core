{-# OPTIONS --safe #-}
module Foundations.Quiver.Fibration.Contravariant where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob}
  {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᵈ⁻} {ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᵈ⁺}
  {ℓ-hetᵈ} (D : SQuiver-onωᵈ C m′ Ob[_]⁻ m′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D) where

  record is-contravariant-fibration : Typeω where
    no-eta-equality
    field
      lift⁻ : ∀{lxs lys lfs} {x : Ob lxs} {y : Ob lys} (p : Hom x y) (v : Ob[ y ]⁺ lfs)
            → is-contr⁻ (Σₜ (Ob[ x ]⁻ lfs) (λ u → Het[ p ] u v))

open is-contravariant-fibration ⦃ ... ⦄ public
{-# DISPLAY is-contravariant-fibration.lift⁻ _ p v = lift⁻ p v #-}
