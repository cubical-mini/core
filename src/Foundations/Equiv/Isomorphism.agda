{-# OPTIONS --safe #-}
module Foundations.Equiv.Isomorphism where

open import Prim.Type

open import Notation.Displayed.Total
open import Notation.Reflexivity
open import Notation.Symmetry

open import Foundations.Equiv.Base
open import Foundations.Invertible.Quasi
open import Foundations.Path.Groupoid
open import Foundations.Pi.Category

open Weak-quasi-inverse
open Path-gpd0
open Fun-cat

is-equiv→quasi-inverse : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B}
                       → is-equiv f → Quasi-inverse f
is-equiv→quasi-inverse fe .from b = fe .equiv-proof b .carrier .carrier
is-equiv→quasi-inverse {f} fe .to-from =
  fun-ext λ a → ap carrier (fe .equiv-proof (f a) .structured (total-ob a refl))
is-equiv→quasi-inverse fe .from-to = fun-ext λ b → sym (fe .equiv-proof b .carrier .structured)

≃→≅ : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
    → A ≃ B → A ≅ B
≃→≅ (total-hom f fe) = total-hom f (is-equiv→quasi-inverse fe)

-- TODO quasi-inverse→is-equiv
-- need retract-is-prop
