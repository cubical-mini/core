{-# OPTIONS --safe #-}
module Iso where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity.Strict
open import Notation.Adjoint
open import Notation.Base
open import Notation.Composition
open import Notation.Duality
open import Notation.Isomorphism
open import Notation.Isomorphism.Reasoning
open import Notation.Symmetry
open import Notation.Unitality.Inner.Strict
open import Notation.Unitality.Outer.Strict
open import Notation.Whiskering.Left.Strict
open import Notation.Whiskering.Right.Strict

open import Foundations.Path.Interface
open import Foundations.Pi.Interface

open Fun-cat
open Path-gpd
module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ≅ B) where private
  to : A → B
  to = e ._≅_.to

  from : B → A
  from = e ._≅_.from

  li : idₜ ＝ from ∘ₜ to
  li = e ._≅_.inverses .Adjoint.η

  ri : to ∘ₜ from ＝ idₜ
  ri = e ._≅_.inverses .Adjoint.ε

module _ {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} (f : A ≅ B) (g : B ≅ C) where

  _ : A ≅ C
  _ = f ∙ g

  _ : B ≅ A
  _ = sym f

  _ : f ᵒᵖ ᵒᵖ ＝ f
  _ = invol f
