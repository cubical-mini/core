{-# OPTIONS --safe #-}
module Foundations.Quiver.Product where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Const
open import Foundations.Quiver.Total.Base

-- binary product
module _ {ma na ℓ-oba⁻ ℓ-oba⁺ ℓ-heta} {Oba⁻ : ob-sig ℓ-oba⁻} {Oba⁺ : ob-sig ℓ-oba⁺}
  (A : Quiver-onω ma na Oba⁻ Oba⁺ ℓ-heta)
  {mb nb ℓ-obb⁻ ℓ-obb⁺ ℓ-hetb} {Obb⁻ : ob-sig ℓ-obb⁻} {Obb⁺ : ob-sig ℓ-obb⁺}
  (B : Quiver-onω mb nb Obb⁻ Obb⁺ ℓ-hetb) where

  infixr 80 _×_
  _×_ : Quiver-onω (ma + mb) (na + nb) (λ _ → Oba⁻ _ ×ₜ Obb⁻ _) (λ _ → Oba⁺ _ ×ₜ Obb⁺ _) _
  _×_ = ∫ A (Constᵈ A B)


-- indexed product
module _ {ℓa} (A : Type ℓa)
  {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : A → ob-sig ℓ-ob⁻} {Ob⁺ : A → ob-sig ℓ-ob⁺}
  (B : (x : A) → Quiver-onω m n (Ob⁻ x) (Ob⁺ x) ℓ-het) where
  private module B x = Quiver-onω (B x)

  ∏ : Quiver-onω m n (λ ls → (x : A) → Ob⁻ x ls) (λ ls → (x : A) → Ob⁺ x ls) _
  ∏ .Quiver-onω.Het P Q = (x : A) → B.Het x (P x) (Q x)


-- cotensor
module _ {ℓa} (A : Type ℓa)
  {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  (B : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het) (open Quiver-onω B) where

  infixr 10 _⋔_
  _⋔_ : Quiver-onω m n (λ ls → A → Ob⁻ ls) (λ ls → A → Ob⁺ ls) _
  _⋔_ = ∏ A (λ _ → B)
