{-# OPTIONS --safe #-}
module Notation.Invertible.Section.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  record Weak-split-epi {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (r : Hom y x) : Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    field
      section      : Hom x y
      section-cell : Splitting C C₂ section r

open Weak-split-epi public
