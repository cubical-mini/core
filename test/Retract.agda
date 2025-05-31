{-# OPTIONS --safe #-}
module Retract where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Retract
open import Notation.Retract.Reasoning

open import Foundations.Pi.Interface
open import Foundations.Path.Interface

open Fun-cat
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (e : A Retract-of B) where private
  to : A → B
  to = e ._Retract-of_.to

  from : B → A
  from = e ._Retract-of_.from

  cell : from ∘ₜ to ＝ idₜ
  cell = e ._Retract-of_.retract-cell

module _ {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (f : A Retract-of B) (g : B Retract-of C) where private

  test : A Retract-of C
  test = f ∙ g

  hmm : A Retract-of A
  hmm = refl

module Iterated
  {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (f : _Retract-of_ ⦃ Retract-Refl ⦄ A B) where private

  to : A Retract-of B
  to = f ._Retract-of_.to

  from : B Retract-of A
  from = f ._Retract-of_.from

  what : to ∙ from ＝ refl ⦃ Retract-Refl ⦄
  what = f ._Retract-of_.retract-cell
