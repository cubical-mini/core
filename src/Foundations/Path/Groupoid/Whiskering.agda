{-# OPTIONS --safe #-}
module Foundations.Path.Groupoid.Whiskering where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Path.Groupoid.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) ⦃ _ : Compω C ⦄ where instance

  Strict-Whisker-l : Whisker-lω C Strict
  Strict-Whisker-l ._◁_ f p i = f ∙ p i

  Strict-Whisker-r : Whisker-rω C Strict
  Strict-Whisker-r ._▷_ p h i = p i ∙ h
  {-# OVERLAPPING Strict-Whisker-l Strict-Whisker-r #-}
