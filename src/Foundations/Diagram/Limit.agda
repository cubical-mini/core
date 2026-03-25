{-# OPTIONS --safe #-}
module Foundations.Diagram.Limit where

open import Foundations.Base
open import Foundations.Discrete.Base
open import Foundations.Lens.Pull

open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-hom⁻}
  (A : HQuiver-onω m Ob⁻ ℓ-hom⁻) (open Quiver-onω A renaming (Het to Hom))
  {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω H)
  ⦃ _ : Refl A ⦄ ⦃ hp : ∀{lys} {y : Ob⁺ lys} → HPull A 0 λ x → Disc (Het x y) ⦄ where

  record Limit {lds} (d : Ob⁺ lds) ℓ-lim : Typeω where
    no-eta-equality
    field
      apex     : Ob⁻ ℓ-lim
      ψ        : Het apex d
      lim-univ : is-universalω⁻ hp ψ
