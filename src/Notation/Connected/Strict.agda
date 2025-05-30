{-# OPTIONS --safe #-}
module Notation.Connected.Strict where

open import Prim.Interval
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Connected
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} where instance

  Connected⁻ : ⦃ Co : Connected C Strict ℓx ℓy ⦄ → Connected C (Strict ²ᵒᵖω) ℓx ℓy
  Connected⁻ ⦃ Co ⦄ .centre = centre ⦃ Co ⦄
  Connected⁻ ⦃ Co ⦄ .centre-cell f i = centre-cell ⦃ Co ⦄ f (~ i)
  {-# INCOHERENT Connected⁻ #-}
