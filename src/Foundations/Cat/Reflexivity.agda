{-# OPTIONS --safe #-}
module Foundations.Cat.Reflexivity where

open import Foundations.Prim.Type

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  where

  record Refl : Typeω where
    no-eta-equality
    field refl : {ℓ : Level} {x : Ob ℓ} → Hom x x

open Refl ⦃ ... ⦄ public

{-# DISPLAY Refl.refl _ = refl #-}
