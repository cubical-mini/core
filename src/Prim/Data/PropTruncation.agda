{-# OPTIONS --safe --erased-cubical #-}
module Prim.Data.PropTruncation where

open import Prim.Kan
open import Prim.Type

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁    : A → ∥ A ∥₁
  squash₁ : (x y : ∥ A ∥₁) → x ＝ y
