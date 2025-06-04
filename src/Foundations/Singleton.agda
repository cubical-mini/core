{-# OPTIONS --safe #-}
module Foundations.Singleton where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Total
open import Notation.Singleton public

open import Foundations.Path.Groupoid.Base

is-central : ∀{ℓ} {A : Type ℓ} (c : A) → Type ℓ
is-central c = Central (Paths _) c

is-contr : ∀{ℓ} (A : Type ℓ) → Type ℓ
is-contr A = Contractible (Paths A)
{-# DISPLAY Total-ob (Enlarge (Paths A)) _ _ = is-contr A #-}

fibre : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) (y : B) → Type (ℓa l⊔ ℓb)
fibre {A} {B} = Fibre (Paths B)
-- FIXME is it possible?
-- {-# DISPLAY Total-ob (Enlarge (Codisc A)) _ lzero = fibre {A} #-}

Singletonₚ : ∀{ℓ} {A : Type ℓ} → A → Type ℓ
Singletonₚ {A} = Singleton (Paths A)

opaque
  is-contr→extend : ∀{ℓ} {A : Type ℓ} → is-contr A → (φ : I) (p : Partial φ A) → A [ φ ↦ p ]
  is-contr→extend C φ p = inS (hcomp φ
    λ { j (φ = i1) → C .structured (p 1=1) j
      ; j (j = i0) → C .carrier
      })

  extend→is-contr : ∀{ℓ} {A : Type ℓ} → (∀ φ (p : Partial φ A) → A [ φ ↦ p ]) → is-contr A
  extend→is-contr ext .carrier        = outS (ext i0 λ())
  extend→is-contr ext .structured x i = outS (ext i λ _ → x)
