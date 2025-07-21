{-# OPTIONS --safe #-}
module Het where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Fan

open import Notation.Refl

module _ {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A → C) (g : B → C) where
  Pullback-on : Quiver-onω 0 (λ _ → A) 0 (λ _ → B) (λ _ _ → ℓc)
  Pullback-on .Quiver-onω.Het a b = f a ＝ g b

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) where private
  Fibre-on = Pullback-on f (λ x → x)

  Fibre : (b : B) → Type (ℓa ⊔ ℓb)
  Fibre b = Fan⁻ Fibre-on b _

  test : ∀{b} (fb : Fibre b) → A
  test = fst
