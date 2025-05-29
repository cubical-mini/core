{-# OPTIONS --safe #-}
module Notation.Associativity.Strict where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓw ℓx ℓy ℓz : Level} ⦃ _ : Comp C ℓw ℓx ℓz ⦄ ⦃ _ : Comp C ℓx ℓy ℓz ⦄ ⦃ _ : Comp C ℓw ℓx ℓy ⦄ ⦃ _ : Comp C ℓw ℓy ℓz ⦄ where instance

  Assoc⁻ : ⦃ A : Assoc C Strict ℓw ℓx ℓy ℓz ⦄ → Assoc C (Strict ²ᵒᵖω) ℓw ℓx ℓy ℓz
  Assoc⁻ ⦃ A ⦄ .assoc f g h i = A .Assoc.assoc f g h (~ i)
  {-# OVERLAPPING Assoc⁻ #-}
