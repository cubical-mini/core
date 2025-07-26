{-# OPTIONS --safe #-}
module Foundations.Quiver.Functions where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Pi public

open import Notation.Pull
open import Notation.Push
open import Notation.Refl
open import Notation.Underlying

Types : ob-sig {m = 1} _
Types (ℓ , _) = Type ℓ

Funs : HQuiver-onω 1 Types _
Funs .Quiver-onω.Het A B = A → B

instance
  Fun-Refl : Refl Funs
  Fun-Refl .refl = id

  Fun-Push : ∀{ℓa} {A : Type ℓa} → HPush Funs 0 (λ T → Disc (A → T))
  Fun-Push .push f g = f ∘ g
  Fun-Push .push-refl {u} _ = u

  Fun-Pull : ∀{ℓb} {B : Type ℓb} → HPull Funs 0 (λ T → Disc (T → B))
  Fun-Pull .pull f g = g ∘ f
  Fun-Pull .pull-refl {v} _ = v

  Funs-HUnderlying : HUnderlying Funs
  Funs-HUnderlying = mk-hunderlying fst id id
