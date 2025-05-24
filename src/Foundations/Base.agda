{-# OPTIONS --safe #-}
module Foundations.Base where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Reflexivity

-- Functions

Fun : {ℓa ℓb : Level} (A : Type ℓa) (B : Type ℓb) → Type (ℓa l⊔ ℓb)
Fun A B = A → B

DFun : {ℓa ℓb : Level} (A : Type ℓa) (B : A → Type ℓb) → Type (ℓa l⊔ ℓb)
DFun A B = (a : A) → B a

instance
  Refl-Fun : Refl (λ ℓ → Type ℓ) Fun
  Refl-Fun .refl x = x

  Comp-Fun : Comp (λ ℓ → Type ℓ) Fun
  Comp-Fun ._∙_ f g x = g (f x)
{-# INCOHERENT Refl-Fun Comp-Fun #-}


-- Useful gadgets

the : {ℓ : Level} (A : Type ℓ) → A → A
the _ a = a

auto : {ℓ : Level} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a
