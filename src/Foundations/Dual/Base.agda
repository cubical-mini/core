module Foundations.Dual.Base where

open import Foundations.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  _ᵒᵖ : Quiver-onω n Ob⁺ m Ob⁻ _
  _ᵒᵖ .Quiver-onω.Het y x = Het x y

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het} (open Quiver-onω C)
  {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻}
  {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺} {ℓ-hetᵈ}
  (D : Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
  where

  _ᵒᵖᵈ : Quiver-onωᵈ (C ᵒᵖ) n′ Ob[_]⁺ m′ Ob[_]⁻ _
  _ᵒᵖᵈ .Quiver-onωᵈ.Het[_] p x′ y′ = Het[ p ] y′ x′
