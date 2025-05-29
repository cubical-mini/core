{-# OPTIONS --safe #-}
module Foundations.Sigma.Base where

open import Prim.Data.Sigma
open import Prim.Type

infixr 80 _×_
_×_ : {ℓa ℓb : Level} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
A × B = Σ A λ _ → B
{-# INLINE _×_ #-}
