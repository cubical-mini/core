{-# OPTIONS --safe #-}
module Foundations.Quiver.Type where

open import Foundations.Quiver.Base

open import Notation.Comp
open import Notation.Refl

Types : ob-sig {m = 1} _
Types (ℓ , _) = Type ℓ

Fun : ∀{ℓa ℓb} → Type ℓa → Type ℓb → Type (ℓa ⊔ ℓb)
Fun A B = A → B

Funs : HQuiver-onω 1 Types _
Funs .Quiver-onω.Het = Fun


id : ∀{ℓ} {A : Type ℓ} → A → A
id x = x

infixr 90 _∘_
_∘_ : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
      (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) (x : A) → C x (f x)
(g ∘ f) x = g (f x)

instance
  Fun-Refl : Reflω Funs
  Fun-Refl .refl = id

  Fun-HComp : HCompω Funs
  Fun-HComp ._∙_ f g = g ∘ f
