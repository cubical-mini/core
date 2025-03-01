{-# OPTIONS --safe #-}
module Foundations.Cat.Reflexivity where

open import Foundations.Prim.Type

open import Foundations.Cat.Structures.Quiver

module _ (C : Quiver) where
  open Quiver C

  record Refl : Typeω where
    no-eta-equality
    field refl : {ℓ : Level} {x : Ob ℓ} → Hom x x

open Refl ⦃ ... ⦄ public

{-# DISPLAY Refl.refl _ = refl #-}
