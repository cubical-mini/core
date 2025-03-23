{-# OPTIONS --safe #-}
module Control.Reflexivity where

open import Prim.Type

open import Control.Structures.Quiver

module _ (C : Quiver) where
  open Quiver C

  record Refl : Typeω where
    no-eta-equality
    field refl : ∀ {ℓ} {x : Ob ℓ} → Hom x x

open Refl ⦃ ... ⦄ public

{-# DISPLAY Refl.refl _ = refl #-}
