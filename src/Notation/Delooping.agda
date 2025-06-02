{-# OPTIONS --safe #-}
module Notation.Delooping where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base

-- \MIB
𝑩 : ∀{ℓ} (A : Type ℓ) → Quiver-on (λ _ → ⊤) (λ _ _ → ℓ)
𝑩 A .Quiver-on.Hom _ _ = A
