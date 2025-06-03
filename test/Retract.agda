{-# OPTIONS --safe --experimental-lazy-instances #-}
module Retract where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Wide
open import Notation.Reflexivity

open import Foundations.Invertible.Retraction
open import Foundations.Pi.Category
open import Foundations.Path.Groupoid

open Fun-cat
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (e : A Retract-of B) where private
  to : A → B
  to = e .hom

  from : B → A
  from = e .preserves .retraction

  cell : from ∘ₜ to ＝ idₜ
  cell = e .preserves .retraction-cell

module _ {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (f : A Retract-of B) (g : B Retract-of C) (h : B Retract-of A) where private
  open Wide-gpd
  open Path-gpd

  test : A Retract-of C
  test = f ∙ g

  hmm : A Retract-of A
  hmm = f ∙ h -- refl breaks this example

module Iterated
  {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  (open Wide-gpd) (open Path-gpd)
  (f : A Retract-of B) where private

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
