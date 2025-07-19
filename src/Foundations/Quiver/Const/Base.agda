{-# OPTIONS --safe #-}
module Foundations.Quiver.Const.Base where

open import Foundations.Quiver.Base

module _ {ma na ℓ-oba⁻ ℓ-oba⁺ ℓ-heta} {Oba⁻ : ob-sig ℓ-oba⁻} {Oba⁺ : ob-sig ℓ-oba⁺}
  (A : Quiver-onω ma na Oba⁻ Oba⁺ ℓ-heta)
  {mb nb ℓ-obb⁻ ℓ-obb⁺ ℓ-hetb} {Obb⁻ : ob-sig ℓ-obb⁻} {Obb⁺ : ob-sig ℓ-obb⁺}
  (B : Quiver-onω mb nb Obb⁻ Obb⁺ ℓ-hetb) where
  private module A = Quiver-onω A
  private module B = Quiver-onω B

  Constᵈ : Quiver-onωᵈ Oba⁻ Oba⁺ A.Het mb nb (λ _ → Obb⁻) (λ _ → Obb⁺) (λ _ _ → ℓ-hetb)
  Constᵈ .Quiver-onωᵈ.Het[_] _ = B.Het
