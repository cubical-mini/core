{-# OPTIONS --safe #-}
module Foundations.Quiver.Fan where

open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  Fan⁺ : ∀{las} (a : Ob⁻ las) lbs → Type (ℓ-ob⁺ lbs ⊔ ℓ-het las lbs)
  Fan⁺ a lbs = Σₜ (Ob⁺ lbs) λ b → Het a b

  Fan⁻ : ∀{lbs} (b : Ob⁺ lbs) las → Type (ℓ-ob⁻ las ⊔ ℓ-het las lbs)
  Fan⁻ b las = Σₜ (Ob⁻ las) λ a → Het a b
