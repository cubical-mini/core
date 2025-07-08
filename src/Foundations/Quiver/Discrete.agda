{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete where

open import Prim.Interval
open import Prim.Kan

open import Foundations.Quiver.Base

module _ {ℓ} (A : I → Type ℓ) where
  Δ : Quiver-onω 0 0 (λ _ → A i0) (λ _ → A i1) (λ _ _ → ℓ)
  Δ .Quiver-onω.Het = Pathᴾ A

  ∇ : Quiver-onω 0 0 (λ _ → A i0) (λ _ → A i1) (λ _ _ → lzero)
  ∇ .Quiver-onω.Het _ _ = ⊤

Disc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 _ _
Disc A = Δ λ _ → A

Codisc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 _ _
Codisc A = ∇ λ _ → A
