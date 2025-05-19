{-# OPTIONS --safe #-}
module Notation.Symmetry where

open import Prim.Type

open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) where

  record Symmetry : Typeω where
    no-eta-equality
    field sym : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy}
              → Hom x y → Hom y x

open Symmetry ⦃ ... ⦄ public

{-# DISPLAY Symmetry.sym _ f = sym f #-}
