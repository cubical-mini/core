{-# OPTIONS --safe #-}
module Iso where

open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Total
open import Notation.Displayed.Wide
open import Notation.Duality
open import Notation.Symmetry

open import Foundations.Invertible.Quasi
open import Foundations.Path.Groupoid
open import Foundations.Pi.Category

open Fun-cat
module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ≅ B) where private
  to : A → B
  to = e .hom

  from : B → A
  from = e .preserves .Weak-quasi-inverse.from

  li : from ∘ₜ to ＝ idₜ
  li = e .preserves .Weak-quasi-inverse.to-from

  ri : to ∘ₜ from ＝ idₜ
  ri = e .preserves .Weak-quasi-inverse.from-to

module _ {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A ≅ B) (g : B ≅ C) where
  open Path-gpd
  open Wide-gpd

  _ : A ≅ C
  _ = f ∙ g

  _ : B ≅ A
  _ = sym f

  _ : f ᵒᵖ ᵒᵖ ＝ f
  _ = invol f
