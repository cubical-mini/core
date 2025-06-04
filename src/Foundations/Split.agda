{-# OPTIONS --safe #-}
module Foundations.Split where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Split public

open import Foundations.Path.Groupoid.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split : ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) (r : Hom x y) → Type (ℓ-hom ℓy ℓy)
  Split = Weak-Split C Strictω

{-# DISPLAY Weak-Split C Strictω = Split C #-}
