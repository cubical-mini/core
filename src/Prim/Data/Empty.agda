{-# OPTIONS --safe #-}
module Prim.Data.Empty where

open import Prim.Type

data ⊥ : Type where

elim : {ℓ : Level} {B : ⊥ → Type ℓ} (x : ⊥) → B x
elim ()

rec : {ℓ : Level} {A : Type ℓ} → ⊥ → A
rec = elim
