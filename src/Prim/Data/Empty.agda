{-# OPTIONS --safe #-}
module Prim.Data.Empty where

open import Prim.Type

data ⊥ₜ : Type where

elim : {ℓ : Level} {B : ⊥ₜ → Type ℓ} (x : ⊥ₜ) → B x
elim ()

rec : {ℓ : Level} {A : Type ℓ} → ⊥ₜ → A
rec = elim
