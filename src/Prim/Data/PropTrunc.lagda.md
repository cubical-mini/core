```agda

{-# OPTIONS --safe #-}

module Prim.Data.PropTrunc where

open import Prim.Base.Type
open import Prim.Base.Interval using ( _＝_ )

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  sq : A → ∥ A ∥
  sq-is-prop : (x y : A) → sq x ＝ sq y
