{-# OPTIONS --safe #-}
module README.Foundations.Pi where

open import Prim.Kan
open import Prim.Type

open import Foundations.Pi.Base
open import Foundations.Path.Base

-- `ap` has good computational properties:
module _ {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {f : A → B} {g : B → C} {x y : A} {p : x ＝ y} where
  ap-comp : ap (g ∘ f) p ＝ ap g (ap f p)
  ap-comp = refl

  ap-id : ap id p ＝ p
  ap-id = refl

  ap-sym : sym (ap f p) ＝ ap f (sym p)
  ap-sym = refl

  ap-refl : ap f (refl {x = x}) ＝ refl
  ap-refl = refl
