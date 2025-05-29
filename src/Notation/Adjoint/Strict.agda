{-# OPTIONS --safe #-}
module Notation.Adjoint.Strict where

open import Prim.Type

open import Notation.Associativity
open import Notation.Adjoint
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

-- NB: can use ω classes if this is too slow
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  {ℓc ℓd : Level} {c : Ob ℓc} {d : Ob ℓd}
  ⦃ _ : Refl C ℓc ⦄ ⦃ _ : Refl C ℓd ⦄
  ⦃ _ : Comp C ℓd ℓd ℓc ⦄ ⦃ _ : Comp C ℓc ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓd ⦄ ⦃ _ : Comp C ℓd ℓc ℓc ⦄ ⦃ _ : Comp C ℓd ℓc ℓd ⦄ ⦃ _ : Comp C ℓc ℓd ℓc ⦄
  ⦃ _ : Whisker-l C C₂ ℓc ℓd ℓd ⦄ ⦃ _ : Whisker-l C C₂ ℓd ℓc ℓc ⦄
  ⦃ _ : Whisker-r C C₂ ℓc ℓc ℓd ⦄ ⦃ _ : Whisker-r C C₂ ℓd ℓd ℓc ⦄
  ⦃ r2 : Refl (Quiver₂ c d) ℓc ⦄ ⦃ r3 : Refl (Quiver₂ d c) ℓd ⦄
  ⦃ c2 : Comp (Quiver₂ c d) ℓc ℓc ℓc ⦄ ⦃ c3 : Comp (Quiver₂ d c) ℓd ℓd ℓd ⦄
  ⦃ _ : Assoc C (C₂ ²ᵒᵖω) ℓc ℓd ℓc ℓd ⦄ ⦃ _ : Unit-i C (C₂ ²ᵒᵖω) ℓc ℓd ⦄ ⦃ _ : Unit-o C C₂ ℓc ℓd ⦄
  ⦃ _ : Assoc C C₂ ℓd ℓc ℓd ℓc ⦄ ⦃ _ : Unit-o C (C₂ ²ᵒᵖω) ℓd ℓc ⦄ ⦃ _ : Unit-i C C₂ ℓd ℓc ⦄ where

  infix 10 _⊣_
  _⊣_ : Hom c d → Hom d c → Type (ℓ-hom ℓc ℓc l⊔ ℓ-hom ℓc ℓd l⊔ ℓ-hom ℓd ℓc l⊔ ℓ-hom ℓd ℓd)
  _⊣_ = Adjoint C C₂ 2-Strict

{-# DISPLAY Adjoint C C₂ 2-Strict L R = _⊣_ {C = C} {C₂ = C₂} L R #-}
