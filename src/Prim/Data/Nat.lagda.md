```agda

{-# OPTIONS --safe #-}

module Prim.Data.Nat where

open import Prim.Base.Type using ( Type )
open import Prim.Base.Interval using ( _≡_ )
open import Agda.Builtin.Nat renaming ( Nat to ℕ ) public

ind-ℕ : ∀ {ℓ} (P : ℕ → Type ℓ)
      → P zero → (∀ k → P k → P (suc k))
      → (n : ℕ) → P n
ind-ℕ P b s zero = b
ind-ℕ P b s (suc n) = s n (ind-ℕ P b s n)

module _ {ℓ} (P : ℕ → Type ℓ) (b : P zero) (s : (∀ k → P k → P (suc k))) where
  indβ-zeroℕ : ind-ℕ P b s zero ≡ b
  indβ-zeroℕ i = b

  indβ-sucℕ : (n : ℕ) → ind-ℕ P b s (suc n) ≡ s n (ind-ℕ P b s n)
  indβ-sucℕ n i = s n (ind-ℕ P b s n)
