{-# OPTIONS --safe #-}
module Foundations.Cat.Underlying where

open import Foundations.Prim.Type

open import Foundations.Cat.Structures.Quiver

module _ (C : Quiver) where
  open Quiver C

  record Underlying : Typeω where
    no-eta-equality
    field
      ℓ-und : Level → Level
      ⌞_⌟   : {ℓ : Level} → Ob ℓ → Type (ℓ-und ℓ)

open Underlying ⦃ ... ⦄ public
{-# DISPLAY Underlying.⌞_⌟ _ x = ⌞ x ⌟ #-}
