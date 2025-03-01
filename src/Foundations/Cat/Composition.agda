{-# OPTIONS --safe #-}
module Foundations.Cat.Composition where

open import Foundations.Prim.Type

open import Foundations.Cat.Structures.Quiver

module _ (C : Quiver) where
  open Quiver C

  record Comp : Typeω where
    no-eta-equality
    infixl 90 _∙_
    field _∙_ : {ℓx ℓy ℓz : Level} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
              → Hom x y → Hom y z → Hom x z

    -- TODO remove?
    infixr 90 _∘_
    _∘_ : {ℓx ℓy ℓz : Level} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
        → Hom y z → Hom x y → Hom x z
    f ∘ g = g ∙ f

open Comp ⦃ ... ⦄ public

{-# DISPLAY Comp._∙_ _ f g = f ∙ g #-}
