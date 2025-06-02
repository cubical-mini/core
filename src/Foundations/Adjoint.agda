{-# OPTIONS --safe #-}
module Foundations.Adjoint where

open import Prim.Type

open import Notation.Adjoint public
open import Notation.Base
open import Notation.Associativity
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Path.Groupoid

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Unit-iω C C₂ ⦄ ⦃ _ : Unit-oω C C₂ ⦄
  ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
  ⦃ _ : Reflω₂ C C₂ ⦄ ⦃ _ : Symmetryω₂ C C₂ ⦄ ⦃ _ : Compω₂ C C₂ ⦄
  where

  infix 10 _⊣_
  _⊣_ : ∀{ℓc ℓd}{c : Ob ℓc} {d : Ob ℓd} → Hom c d → Hom d c → Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc l⊔ ℓ-hom ℓd ℓd)
  _⊣_ = Adjoint C C₂ 2-Strict

{-# DISPLAY Adjoint C C₂ 2-Strict {_} {_} {c} {d} L R = _⊣_ {C = C} {C₂ = C₂} {c} {d} L R #-}
