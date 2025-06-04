{-# OPTIONS --safe #-}
module Foundations.Idempotent where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Idempotent public

open import Foundations.Path.Groupoid.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ : Level} ⦃ _ : Comp C ℓ ℓ ℓ ⦄ where

  Idem : {x : Ob ℓ} (e : Hom x x) → Type (ℓ-hom ℓ ℓ)
  Idem = Weak-Idem C Strictω

{-# DISPLAY Weak-Idem C Strictω = Idem C #-}
