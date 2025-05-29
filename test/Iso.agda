{-# OPTIONS --safe #-}
module Iso where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity.Strict
open import Notation.Adjoint
open import Notation.Adjoint.Isomorphism
open import Notation.Base
open import Notation.Unitality.Inner.Strict
open import Notation.Unitality.Outer.Strict
open import Notation.Whiskering.Left.Strict
open import Notation.Whiskering.Right.Strict

open import Foundations.Path.Interface
open import Foundations.Pi.Interface

module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ≅ B) where
  to : A → B
  to = e ._≅_.to

  from : B → A
  from = e ._≅_.from

  li : idₜ ＝ from ∘ₜ to
  li = e ._≅_.inverses .Adjoint.η

  ri : to ∘ₜ from ＝ idₜ
  ri = e ._≅_.inverses .Adjoint.ε
