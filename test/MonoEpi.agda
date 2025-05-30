{-# OPTIONS --safe #-}
module MonoEpi where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity.Strict
open import Notation.Adjoint
open import Notation.Adjoint.Isomorphism
open import Notation.Base
open import Notation.Section
open import Notation.Section.Strict
open import Notation.Retraction
open import Notation.Retraction.Strict
open import Notation.Unitality.Inner.Strict
open import Notation.Unitality.Outer.Strict
open import Notation.Whiskering.Left.Strict
open import Notation.Whiskering.Right.Strict

open import Foundations.Path.Interface
open import Foundations.Pi.Interface

module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ↠! B) where private
  to : A → B
  to = e ._↠!_.to

  from : B → A
  from = e ._↠!_.has-split-epi .Weak-split-epi.section

  check : to ∘ₜ from ＝ idₜ
  check = e ._↠!_.has-split-epi .Weak-split-epi.section-cell


module _ {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} (e : A ↣! B) where private
  to : A → B
  to = e ._↣!_.to

  from : B → A
  from = e ._↣!_.has-split-mono .Weak-split-mono.retraction

  check : from ∘ₜ to ＝ idₜ
  check = e ._↣!_.has-split-mono .Weak-split-mono.retraction-cell
