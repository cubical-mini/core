{-# OPTIONS --safe #-}
module Control.Underlying where

open import Prim.Type

open import Control.Structures.Quiver

module _ (C : Quiver) where
  open Quiver C

  record Underlying : Typeω where
    no-eta-equality
    field
      ℓ-und : Level → Level
      ⌞_⌟   : ∀ {ℓ} → Ob ℓ → Type (ℓ-und ℓ)

open Underlying ⦃ ... ⦄ public
{-# DISPLAY Underlying.⌞_⌟ _ x = ⌞ x ⌟ #-}
