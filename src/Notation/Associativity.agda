{-# OPTIONS --safe #-}
module Notation.Associativity where

open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) ⦃ _ : Comp Ob Hom ⦄
  (_~_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)) where

  record Assoc : Typeω where
    no-eta-equality
    field assoc : {ℓw ℓx ℓy ℓz : Level} {w : Ob ℓw} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
                  (f : Hom w x) (g : Hom x y) (h : Hom y z)
                → f ∙ (g ∙ h) ~ (f ∙ g) ∙ h

open Assoc ⦃ ... ⦄ public

{-# DISPLAY Assoc.assoc _ f g h = assoc f g h #-}
