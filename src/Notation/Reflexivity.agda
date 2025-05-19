{-# OPTIONS --safe #-}
module Notation.Reflexivity where

open import Prim.Type

open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) where

  record Refl : Typeω where
    no-eta-equality
    field refl : {ℓ : Level} {x : Ob ℓ} → Hom x x

open Refl ⦃ ... ⦄ public

{-# DISPLAY Refl.refl _ = refl #-}
