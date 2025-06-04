{-# OPTIONS --safe #-}
module Foundations.Pi.Category where

open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Idempotent
open import Notation.Reflexivity
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

open import Foundations.Idempotent
open import Foundations.Path.Base
  using ()
  renaming (refl to reflₚ)
open import Foundations.Path.Groupoid.Base

open import Foundations.Pi.Base
  public
  renaming ( id  to idₜ
           ; _∘_ to _∘ₜ_
           )

Funs : Quiver-on (λ ℓ → Type ℓ) _l⊔_
Funs .Quiver-on.Hom = Fun

module Fun-cat where instance
  Fun-Refl : Reflω Funs
  Fun-Refl .refl = idₜ

  Fun-Comp : Compω Funs
  Fun-Comp .Comp._∙_ f g x = g (f x)

  Fun-Assoc : Assocω Funs Strictω
  Fun-Assoc .Assoc.assoc _ _ _ = reflₚ

  Fun-Unit-i : Unit-iω Funs Strictω
  Fun-Unit-i .id-i _ = reflₚ

  Fun-Unit-o : Unit-oω Funs Strictω
  Fun-Unit-o .id-o _ = reflₚ

  Fun-Refl-Idem : ∀{ℓ} {A : Type ℓ} → Idem Funs {x = A} refl
  Fun-Refl-Idem .idem = reflₚ

  {-# OVERLAPPING
    Fun-Refl Fun-Comp
    Fun-Assoc Fun-Unit-i Fun-Unit-o
    Fun-Refl-Idem
  #-}
