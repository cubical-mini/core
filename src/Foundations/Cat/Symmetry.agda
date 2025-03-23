{-# OPTIONS --safe #-}
module Control.Symmetry where

open import Prim.Type

open import Control.Structures.Quiver

module _ (C : Quiver) where
  open Quiver C

  record Symmetry : Typeω where
    no-eta-equality
    field sym : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy}
              → Hom x y → Hom y x

open Symmetry ⦃ ... ⦄ public

{-# DISPLAY Symmetry.sym _ f = sym f #-}
