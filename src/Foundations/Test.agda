{-# OPTIONS --safe --default-level #-}
module Foundations.Test where

open import Foundations.Base

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)

data _≤_ : ℕ → ℕ → Type where
  instance
    z≤ : {n : ℕ} → 0 ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-trans : {m n k : ℕ} → m ≤ n → n ≤ k → m ≤ k
≤-trans z≤      z≤      = z≤
≤-trans z≤      (s≤s q) = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-refl : {n : ℕ} → n ≤ n
≤-refl {(zero)} = z≤
≤-refl {suc n} = s≤s ≤-refl

min : ℕ → ℕ → ℕ
min zero    _ = zero
min (suc m) zero = zero
min (suc m) (suc n) = suc (min m n)

min-l : (m n : ℕ) → min m n ≤ m
min-l zero n = z≤
min-l (suc m) zero = z≤
min-l (suc m) (suc n) = s≤s (min-l m n)

min-r : (m n : ℕ) → min m n ≤ n
min-r zero n = z≤
min-r (suc m) zero = z≤
min-r (suc m) (suc n) = s≤s (min-r m n)

open import Agda.Builtin.Bool

ℕQ : Quiver
ℕQ = mk-quiver (λ _ → ℕ) _≤_

instance
  ℕ-Comp : Comp ℕQ
  ℕ-Comp ._∙_ = ≤-trans

  ℕ-Refl : Refl ℕQ
  ℕ-Refl .refl = ≤-refl

  ℕ-whatever : Indexed-products ℕQ Bool
  ℕ-whatever .∏ f = min (f false) (f true)
  ℕ-whatever .Indexed-products.has-ip .π false = min-l _ _
  ℕ-whatever .Indexed-products.has-ip .π true = min-r _ _
  ℕ-whatever .Indexed-products.has-ip .Indexed-product.has-is-ip .is-indexed-product.tuple f = {!!}
  ℕ-whatever .Indexed-products.has-ip .Indexed-product.has-is-ip .is-indexed-product.commute = {!!}
  ℕ-whatever .Indexed-products.has-ip .Indexed-product.has-is-ip .is-indexed-product.unique f p = {!!}

F : Bool → ℕ
F false = 5
F true  = 7

_ : ∏ F ＝ 5
_ = reflₚ
