{-# OPTIONS --safe #-}
module Notation.Unitality.Outer.Strict where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Outer

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓx ℓy ℓy ⦄ where instance

  Unit-o⁻ : ⦃ UO : Unit-o C Strict ℓx ℓy ⦄ → Unit-o C (Strict ²ᵒᵖω) ℓx ℓy
  Unit-o⁻ ⦃ UO ⦄ .id-o f i = UO .Unit-o.id-o f (~ i)
  {-# OVERLAPPING Unit-o⁻ #-}
