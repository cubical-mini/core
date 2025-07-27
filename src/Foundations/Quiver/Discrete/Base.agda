{-# OPTIONS --safe #-}
module Foundations.Quiver.Discrete.Base where

open import Prim.Interval public
open import Prim.Kan public

open import Foundations.Quiver.Base

module _ {ℓ} (A : I → Type ℓ) where
  Δ : Quiver-onω 0 (λ _ → A i0) 0 (λ _ → A i1) (λ _ _ → ℓ)
  Δ .Quiver-onω.Het = Pathᴾ A

Disc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 (λ _ → A) (λ _ _ → ℓ)
Disc A = Δ λ _ → A

module _ {ℓa ℓb} {A : I → Type ℓa} (B : (i : I) → A i → Type ℓb) where
  Δᵈ : Quiver-onωᵈ (Δ A) 0 (λ a⁻ _ → B i0 a⁻) 0 (λ a⁺ _ → B i1 a⁺) (λ _ _ _ _ → ℓb)
  Δᵈ .Quiver-onωᵈ.Het[_] p = Pathᴾ (λ i → B i (p i))

module _ {ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb) where
  Discᵈ : HQuiver-onωᵈ (Disc A) 0 (λ a _ → B a) (λ _ _ _ _ → ℓb)
  Discᵈ = Δᵈ λ _ → B
