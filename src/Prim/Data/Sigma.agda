{-# OPTIONS --safe #-}
module Prim.Data.Sigma where

open import Prim.Type

open import Agda.Builtin.Sigma
  renaming (_,_ to infixr 40 _,_)
  public

infixr 80 _×_
_×_ : ∀{ℓa ℓb} → Type ℓa → Type ℓb → Type (ℓa ⊔ ℓb)
A × B = Σ A (λ _ → B)
