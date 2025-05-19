{-# OPTIONS --safe #-}
module Prim.Data.Sigma where

open import Prim.Type

open import Agda.Builtin.Sigma public
  renaming (Σ to Σₜ)

infixr 80 _×ₜ_
_×ₜ_ : {ℓa ℓb : Level} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
A ×ₜ B = Σₜ A λ _ → B
{-# INLINE _×ₜ_ #-}
