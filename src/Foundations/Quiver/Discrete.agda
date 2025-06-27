{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete where

open import Prim.Interval
open import Prim.Kan

open import Foundations.Quiver.Base

module _ {ℓ} (A : I → Type ℓ) where
  Disc : Quiver-onω 0 0 (λ _ → A i0) (λ _ → A i1) (λ _ _ → ℓ)
  Disc .Quiver-onω.Het = Pathᴾ A

  Codisc : Quiver-onω 0 0 (λ _ → A i0) (λ _ → A i1) (λ _ _ → lzero)
  Codisc .Quiver-onω.Het _ _ = ⊤

Δ : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 _ _
Δ A = Disc λ _ → A

∇ : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 _ _
∇ A = Codisc λ _ → A
