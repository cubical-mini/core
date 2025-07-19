{-# OPTIONS --safe #-}
module Foundations.Quiver.Exponential where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Const.Base
open import Foundations.Quiver.Section.Base

open import Notation.Refl

module _ {ma na ℓ-oba⁻ ℓ-oba⁺ ℓ-heta} {Oba⁻ : ob-sig ℓ-oba⁻} {Oba⁺ : ob-sig ℓ-oba⁺}
  (A : Quiver-onω ma na Oba⁻ Oba⁺ ℓ-heta)
  {mb nb ℓ-obb⁻ ℓ-obb⁺ ℓ-hetb} {Obb⁻ : ob-sig ℓ-obb⁻} {Obb⁺ : ob-sig ℓ-obb⁺}
  (B : Quiver-onω mb nb Obb⁻ Obb⁺ ℓ-hetb) where

  infixr 0 _⇒_
  _⇒_ : Quiver-onω (ma + mb) (na + nb) (λ ls → Oba⁻ _ → Obb⁻ _) (λ ls → Oba⁺ _ → Obb⁺ _) _
  _⇒_ = Π A (Constᵈ A B)
