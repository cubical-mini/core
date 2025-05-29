{-# OPTIONS --safe #-}
module Notation.Unitality.Inner.Strict where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Inner

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓx ℓy ⦄ where instance

  Unit-i⁻ : ⦃ UI : Unit-i C Strict ℓx ℓy ⦄ → Unit-i C (Strict ²ᵒᵖω) ℓx ℓy
  Unit-i⁻ ⦃ UI ⦄ .id-i f i = UI .Unit-i.id-i f (~ i)
  {-# OVERLAPPING Unit-i⁻ #-}
