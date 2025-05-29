{-# OPTIONS --safe #-}
module Notation.Whiskering.Right.Strict where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Strict
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy ℓz : Level} ⦃ _ : Comp C ℓx ℓy ℓz ⦄ where instance

  Strict-Whisker-r : Whisker-r C Strict ℓx ℓy ℓz
  Strict-Whisker-r ._▷_ p h i = p i ∙ h
  {-# OVERLAPPING Strict-Whisker-r #-}
