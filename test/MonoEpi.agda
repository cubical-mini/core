{-# OPTIONS --safe #-}
module MonoEpi where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Total
open import Notation.Reflexivity
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

open import Foundations.Invertible.Retraction
open import Foundations.Invertible.Section
open import Foundations.Path.Groupoid
open import Foundations.Pi.Category

open Fun-cat
module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ↠! B) where private
  to : A → B
  to = e .hom

  from : B → A
  from = e .preserves .section

  check : to ∘ₜ from ＝ idₜ
  check = e .preserves .section-cell


module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ↣! B) where private
  to : A → B
  to = e .hom

  from : B → A
  from = e .preserves .retraction

  check : from ∘ₜ to ＝ idₜ
  check = e .preserves .retraction-cell
