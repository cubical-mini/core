{-# OPTIONS --safe #-}
module Foundations.Quiver.Const.Base where

open import Foundations.Quiver.Base

module _ {ma ℓ-oba⁻} {Oba⁻ : ob-sig ℓ-oba⁻} {na ℓ-oba⁺} {Oba⁺ : ob-sig ℓ-oba⁺}
  {ℓ-heta} (A : Quiver-onω ma Oba⁻ na Oba⁺ ℓ-heta)
  {mb ℓ-obb⁻} {Obb⁻ : ob-sig ℓ-obb⁻} {nb ℓ-obb⁺} {Obb⁺ : ob-sig ℓ-obb⁺}
  {ℓ-hetb} (B : Quiver-onω mb Obb⁻ nb Obb⁺ ℓ-hetb) where
  private module A = Quiver-onω A
  private module B = Quiver-onω B

  Const : Quiver-onωᵈ A mb (λ _ → Obb⁻) nb (λ _ → Obb⁺) (λ _ _ → ℓ-hetb)
  Const .Quiver-onωᵈ.Het[_] _ = B.Het
