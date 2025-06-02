{-# OPTIONS --safe #-}
module Notation.Idempotent where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  {ℓ : Level} ⦃ _ : Comp C ℓ ℓ ℓ ⦄ where

  record Idem {x : Ob ℓ} (e : Hom x x) : Type (ℓ-hom ℓ ℓ) where
    no-eta-equality
    field idem : 2-Hom (e ∙ e) e

open Idem ⦃ ... ⦄ public

{-# DISPLAY Idem.idem _ e = idem e #-}
