{-# OPTIONS --safe #-}
module Notation.Reflexivity where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where

  record Refl ℓ : Type (ℓ-ob ℓ l⊔ ℓ-hom ℓ ℓ) where
    no-eta-equality
    field refl : {x : Ob ℓ} → Hom x x

  Reflω : Typeω
  Reflω = {ℓ : Level} → Refl ℓ

open Refl ⦃ ... ⦄ public

{-# DISPLAY Refl.refl _ = refl #-}
