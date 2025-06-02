{-# OPTIONS --safe #-}
module Iso where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Adjoint
open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Wide
open import Notation.Duality
open import Notation.Invertibility.Quasi
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Path.Interface
open import Foundations.Pi.Interface

open Fun-cat
module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ≅ B) where private
  to : A → B
  to = e .hom

  from : B → A
  from = e .preserves .Quasi-inverse.from

  li : from ∘ₜ to ＝ idₜ
  li = e .preserves .Quasi-inverse.to-from

  ri : to ∘ₜ from ＝ idₜ
  ri = e .preserves .Quasi-inverse.from-to

module _ {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A ≅ B) (g : B ≅ C) where
  open Wide-gpd

  _ : A ≅ C
  _ = f ∙ g

  _ : B ≅ A
  _ = sym f

  _ : f ᵒᵖ ᵒᵖ ＝ f
  _ = invol f
