{-# OPTIONS --safe #-}
module Notation.Composition where

open import Prim.Type

open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) where

  record Comp : Typeω where
    no-eta-equality
    infixl 90 _∙_
    field
      _∙_ : {ℓx ℓy ℓz : Level} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
          → Hom x y → Hom y z → Hom x z

open Comp ⦃ ... ⦄ public

{-# DISPLAY Comp._∙_ _ f g = f ∙ g #-}
