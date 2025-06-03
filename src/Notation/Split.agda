{-# OPTIONS --safe #-}
module Notation.Split where

open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Idempotent
open import Notation.Reflexivity
open import Notation.Reasoning.Category
open import Notation.Reasoning.Semicategory
open import Notation.Split.Base public
open import Notation.Symmetry
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Unit-oω C C₂ ⦄
  ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
  ⦃ _ : Symmetryω₂ C C₂ ⦄ ⦃ _ : Compω₂ C C₂ ⦄
  {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} {s : Hom y x} {r : Hom x y}
  ⦃ _ : Weak-Split C C₂ s r ⦄ where instance

  Weak-split→Weak-idem : Weak-Idem C C₂ (r ∙ s)
  Weak-split→Weak-idem .idem = centralize ∙ collapse-l split
  {-# INCOHERENT Weak-split→Weak-idem #-}
