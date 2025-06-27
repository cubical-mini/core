{-# OPTIONS --safe #-}
module Foundations.Quiver.Fan where

open import Foundations.Quiver.Base

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (C : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω C) where

  Fan⁺ : ∀{las} (a : Ob⁻ las) lbs → Type (ℓ-ob⁺ lbs ⊔ ℓ-het las lbs)
  Fan⁺ a lbs = Σₜ (Ob⁺ lbs) λ b → Het a b

  Fan⁻ : ∀{lbs} (b : Ob⁺ lbs) las → Type (ℓ-ob⁻ las ⊔ ℓ-het las lbs)
  Fan⁻ b las = Σₜ (Ob⁻ las) λ a → Het a b
