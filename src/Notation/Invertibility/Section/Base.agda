{-# OPTIONS --safe #-}
module Notation.Invertibility.Section.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  record Split-epi {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (r : Hom y x) : Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    field
      section      : Hom x y
      section-cell : section section-of r

open Split-epi public
