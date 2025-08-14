{-# OPTIONS --safe #-}
module Foundations.Quiver.Exponential where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Const
open import Foundations.Quiver.Section

module _ {ma ℓ-oba⁻} {Oba⁻ : ob-sig ℓ-oba⁻} {na ℓ-oba⁺} {Oba⁺ : ob-sig ℓ-oba⁺}
  {ℓ-heta} (A : Quiver-onω ma Oba⁻ na Oba⁺ ℓ-heta)
  {mb ℓ-obb⁻} {Obb⁻ : ob-sig ℓ-obb⁻} {nb ℓ-obb⁺} {Obb⁺ : ob-sig ℓ-obb⁺}
  {ℓ-hetb} (B : Quiver-onω mb Obb⁻ nb Obb⁺ ℓ-hetb) where

  infixr 0 _→̫_
  _→̫_ : Quiver-onω (ma + mb) (λ ls → Oba⁻ _ → Obb⁻ _) (na + nb) (λ ls → Oba⁺ _ → Obb⁺ _) _
  _→̫_ = Π̫[ Const A B ]
