{-# OPTIONS --safe #-}
module Foundations.Base where

open import Prim.Type

-- Useful gadgets

the : ∀{ℓ} (A : Type ℓ) → A → A
the _ a = a

auto : ∀{ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a
