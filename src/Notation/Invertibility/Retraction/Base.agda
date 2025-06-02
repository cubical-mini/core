{-# OPTIONS --safe #-}
module Notation.Invertibility.Retraction.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  record Split-mono {ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (s : Hom y x) : Type (ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓy) where
    no-eta-equality
    field
      retraction      : Hom x y
      retraction-cell : retraction retraction-of s

open Split-mono public
