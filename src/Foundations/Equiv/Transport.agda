{-# OPTIONS --safe #-}
module Foundations.Equiv.Transport where

open import Prim.Interval
open import Prim.Type

open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Total

open import Foundations.Equiv.Base
open import Foundations.Path.Coe
open import Foundations.Path.Groupoid
open import Foundations.Path.Transport
open import Foundations.Pi.Category

module _ {ℓ̂ : I → Level} (P : (i : I) → Type (ℓ̂ i)) where

  private
    L = P i0
    R = P i1

    g = coei→1 P

  open Fun-cat
  transport-line-is-equiv : ∀ i → is-equiv (g i)
  transport-line-is-equiv i =
    coe1→i (λ j → is-equiv (g j)) i reflᵈ

  transport-line-equiv : ∀ i → P i ≃ R
  transport-line-equiv i .hom = g i
  transport-line-equiv i .preserves = transport-line-is-equiv i

  line→is-equiv : is-equiv (g i0)
  line→is-equiv = transport-line-is-equiv i0

  line→≃ : L ≃ R
  line→≃ = transport-line-equiv i0

transport-is-equiv : ∀{ℓ} {A B : Type ℓ}
                     (p : A ＝ B) → is-equiv (transport p)
transport-is-equiv p = line→is-equiv (λ i → p i)

subst-is-equiv : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                 {x y : A} (p : x ＝ y) → is-equiv (subst B p)
subst-is-equiv {B} p = transport-is-equiv (ap B p)

subst-≃ : ∀{ℓa ℓb} {A : Type ℓa} (B : A → Type ℓb)
          {x y : A} (p : x ＝ y) → B x ≃ B y
subst-≃ P p .hom = subst P p
subst-≃ P p .preserves = subst-is-equiv p
