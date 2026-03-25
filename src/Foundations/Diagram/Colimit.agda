{-# OPTIONS --safe #-}
module Foundations.Diagram.Colimit where

open import Foundations.Base
open import Foundations.Discrete.Base
open import Foundations.Lens.Push

open import Notation.Refl

module _ {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁺}
  (B : HQuiver-onω n Ob⁺ ℓ-hom⁺) (open Quiver-onω B renaming (Het to Hom))
  {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {ℓ-het}
  (H : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω H)
  ⦃ _ : Refl B ⦄ ⦃ hp : ∀{lxs} {x : Ob⁻ lxs} → HPush B 0 (λ y → Disc (Het x y)) ⦄ where

  record Colimit {lds} (d : Ob⁻ lds) ℓ-col : Typeω where
    no-eta-equality
    field
      coapex     : Ob⁺ ℓ-col
      ψ          : Het d coapex
      colim-univ : is-universalω⁺ hp ψ
