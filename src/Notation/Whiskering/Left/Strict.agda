{-# OPTIONS --safe #-}
module Notation.Whiskering.Left.Strict where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Strict
open import Notation.Whiskering.Left

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy ℓz : Level} ⦃ _ : Comp C ℓx ℓy ℓz ⦄ where instance

  Strict-Whisker-l : Whisker-l C Strict ℓx ℓy ℓz
  Strict-Whisker-l ._◁_ f p i = f ∙ p i
  {-# OVERLAPPING Strict-Whisker-l #-}
