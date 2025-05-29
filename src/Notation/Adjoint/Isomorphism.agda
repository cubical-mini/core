{-# OPTIONS --safe #-}
module Notation.Adjoint.Isomorphism where


open import Prim.Type

open import Notation.Associativity
open import Notation.Associativity.Strict
open import Notation.Adjoint
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Trivial
open import Notation.Unitality.Inner
open import Notation.Unitality.Inner.Strict
open import Notation.Unitality.Outer
open import Notation.Unitality.Outer.Strict
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Path.Interface

-- NB: can use ω classes if this is too slow
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓc ℓd : Level} (c : Ob ℓc) (d : Ob ℓd)
  ⦃ _ : Refl C ℓc ⦄ ⦃ _ : Refl C ℓd ⦄
  ⦃ _ : Comp C ℓd ℓd ℓc ⦄ ⦃ _ : Comp C ℓc ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓd ⦄
  ⦃ _ : Comp C ℓd ℓc ℓc ⦄ ⦃ _ : Comp C ℓd ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓc ⦄
  ⦃ _ : Whisker-l C Strict ℓc ℓd ℓd ⦄ ⦃ _ : Whisker-l C Strict ℓd ℓc ℓc ⦄
  ⦃ _ : Whisker-r C Strict ℓc ℓc ℓd ⦄ ⦃ _ : Whisker-r C Strict ℓd ℓd ℓc ⦄
  ⦃ _ : Assoc C Strict ℓd ℓc ℓd ℓc ⦄ ⦃ _ : Unit-o C Strict ℓc ℓd ⦄ ⦃ _ : Unit-i C Strict ℓd ℓc ⦄
  ⦃ _ : Assoc C Strict ℓc ℓd ℓc ℓd ⦄ ⦃ _ : Unit-i C Strict ℓc ℓd ⦄ ⦃ _ : Unit-o C Strict ℓd ℓc ⦄
  where

  infix 10 _≅_
  record _≅_ : Type (ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc l⊔ ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓd ℓd) where
    no-eta-equality
    field
      to       : Hom c d
      from     : Hom d c
      inverses : Adjoint C Strict 3-Trivial to from
