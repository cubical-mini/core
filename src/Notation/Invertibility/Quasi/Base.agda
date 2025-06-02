{-# OPTIONS --safe #-}
module Notation.Invertibility.Quasi.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄
  where

  record Quasi-inverse {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (to : Hom x y)
    : Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓy) where
    constructor mk-quasi-inverse
    no-eta-equality
    field
      from    : Hom y x
      to-from : from retraction-of to
      from-to : from section-of    to
