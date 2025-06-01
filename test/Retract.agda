{-# OPTIONS --safe #-}
module Retract where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Reflexivity
open import Notation.Retract
open import Notation.Retraction

open import Foundations.Pi.Interface
open import Foundations.Path.Interface

open Fun-cat
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (e : A Retract-of B) where private
  to : A → B
  to = e .hom

  from : B → A
  from = e .preserves .retraction

  cell : from ∘ₜ to ＝ idₜ
  cell = e .preserves .retraction-cell

module _ {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (f : A Retract-of B) (g : B Retract-of C) where private
  open Retract-quiver

  test : A Retract-of C
  test = f ∙ g

  hmm : A Retract-of A
  hmm = refl

module Iterated
  {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (open Retract-quiver)
  (f : _Retract-of_ ⦃ Retract-Refl ⦄ ⦃ Retract-Comp ⦄ ⦃ Retract-Refl ⦄ A B) where private

  to : A ↣! B
  to = f .hom

  from : B ↣! A
  from = f .preserves .retraction

  _ : Path (A ↣! A) (to ∙ from) refl
  _ = f .preserves .retraction-cell

  to′ : A → B
  to′ = f .hom .hom

  from′ : B → A
  from′ = f .hom .preserves .retraction

  _ : to′ ∙ from′ ＝ refl
  _ = f .hom .preserves .retraction-cell
