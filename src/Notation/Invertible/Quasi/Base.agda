{-# OPTIONS --safe #-}
module Notation.Invertible.Quasi.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄
  where

  record Weak-quasi-inverse {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (to : Hom x y)
    : Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓy) where
    constructor mk-quasi-inverse
    no-eta-equality
    field
      from    : Hom y x
      to-from : Splitting C C₂ to from
      from-to : Splitting C C₂ from to
