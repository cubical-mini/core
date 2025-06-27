{-# OPTIONS --safe #-}
module Het where

open import Prim.Interval
open import Prim.Kan

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component.Base
open import Foundations.Quiver.Component.Groupoid
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Fan

open import Notation.Comp.Pre
open import Notation.Refl

Types : ob-sig {n = 1} _
Types (ℓ , tt) = Type ℓ

Funs-on : HQuiver-onω 1 Types _
Funs-on .Quiver-onω.Het A B = A → B

Funs : Quiverω 1 1 _ _ _
Funs .Quiverω.Ob⁻ = Types
Funs .Quiverω.Ob⁺ = Types
Funs .has-quiver-onω = Funs-on

module _ {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A → C) (g : B → C) where
  Pullback-on : Quiver-onω 0 0 (λ _ → A) (λ _ → B) (λ _ _ → ℓc)
  Pullback-on .Quiver-onω.Het a b = f a ＝ g b

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) where private
  Fibre-on = Pullback-on f (λ x → x)

  Fibre : (b : B) → Type (ℓa ⊔ ℓb)
  Fibre b = Fan⁻ Fibre-on b _

  test : ∀{b} (fb : Fibre b) → A
  test = fst
