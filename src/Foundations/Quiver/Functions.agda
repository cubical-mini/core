{-# OPTIONS --safe #-}
module Foundations.Quiver.Functions where

open import Foundations.Pi public
open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Lens.Pull.Base
open import Foundations.Quiver.Lens.Push.Base

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
  Fun-Push ._▷_ f g = g ∘ f
  Fun-Push .push-refl {u} _ = u

  Fun-Pull : ∀{ℓb} {B : Type ℓb} → HPull Funs 0 (λ T → Disc (T → B))
  Fun-Pull ._◁_ f g = g ∘ f
  Fun-Pull .pull-refl {v} _ = v

  Funs-HUnderlying : HUnderlying Funs
  Funs-HUnderlying = mk-hunderlying fst id id
