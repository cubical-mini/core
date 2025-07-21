{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Base where

open import Foundations.Quiver.Base

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  Op : Quiver-onω n Ob⁺ m Ob⁻ _
  Op .Quiver-onω.Het y x = Het x y

  module _ {m′ ℓ-obᵈ⁻} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻}
    {n′ ℓ-obᵈ⁺} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺} {ℓ-hetᵈ}
    (D : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ Ob[_]⁻ n′ Ob[_]⁺ ℓ-hetᵈ) (open Quiver-onωᵈ D)
    where

    Opᵈ : Quiver-onωᵈ Ob⁺ Ob⁻ _ n′ Ob[_]⁺ m′ Ob[_]⁻ _
    Opᵈ .Quiver-onωᵈ.Het[_] p x′ y′ = Het[ p ] y′ x′
