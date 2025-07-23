{-# OPTIONS --safe #-}
module Foundations.Quiver.Codiscrete where

open import Prim.Interval

open import Foundations.Quiver.Base

module _ {ℓ} (A : I → Type ℓ) where
  ∇ : Quiver-onω 0 (λ _ → A i0) 0 (λ _ → A i1) (λ _ _ → lzero)
  ∇ .Quiver-onω.Het _ _ = ⊤ₜ

Codisc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 (λ _ → A) (λ _ _ → lzero)
Codisc A = ∇ λ _ → A
