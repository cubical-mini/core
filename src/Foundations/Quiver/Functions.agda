{-# OPTIONS --safe #-}
module Foundations.Quiver.Functions where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Pi public

open import Notation.Profunctor
open import Notation.Refl
open import Notation.Underlying

Types : ob-sig {m = 1} _
Types (ℓ , _) = Type ℓ

Funs : HQuiver-onω 1 Types _
Funs .Quiver-onω.Het A B = A → B

instance
  Fun-Refl : Refl Funs
  Fun-Refl .refl = id

  Fun-HProfunctor : HProfunctor Funs Funs 0 (λ A B → Disc (A → B))
  Fun-HProfunctor .dimap f g h = g ∘ h ∘ f
  Fun-HProfunctor .dimap-refl {u} _ = u

  Funs-HUnderlying : HUnderlying Funs
  Funs-HUnderlying = mk-hunderlying fst id id
