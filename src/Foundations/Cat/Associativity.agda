{-# OPTIONS --safe #-}
module Control.Associativity where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Structures.Quiver

module _ {C : Quiver} ⦃ _ : Comp C ⦄ where
  open Quiver C

  record Assoc : Typeω where
    no-eta-equality
    field assoc : {ℓw ℓx ℓy ℓz : Level} {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
                  (f : Hom w x) (g : Hom x y) (h : Hom y z)
                → f ∙ (g ∙ h) ≡ (f ∙ g) ∙ h

open Assoc ⦃ ... ⦄ public

{-# DISPLAY Assoc.assoc _ f g h = assoc f g h #-}
