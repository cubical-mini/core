{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete.Base where

open import Prim.Interval public
open import Prim.Kan public

open import Foundations.Quiver.Base

module _ {ℓ} (A : I → Type ℓ) where
  Δ : Quiver-onω 0 (λ _ → A i0) 0 (λ _ → A i1) (λ _ _ → ℓ)
  Δ .Quiver-onω.Het = Pathᴾ A

Disc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 (λ _ → A) (λ _ _ → ℓ)
Disc A = Δ λ _ → A
