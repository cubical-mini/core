{-# OPTIONS --safe #-}
module Foundations.Cat.Symmetry where

open import Foundations.Prim.Type

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  where

  record Symmetry : Typeω where
    no-eta-equality
    field sym : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy}
              → Hom x y → Hom y x

open Symmetry ⦃ ... ⦄ public

{-# DISPLAY Symmetry.sym _ f = sym f #-}
