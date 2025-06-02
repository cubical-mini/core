{-# OPTIONS --safe #-}
module Notation.Unitality.Outer where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  (ℓx ℓy : Level) ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓx ℓy ℓy ⦄ where

  record Unit-o : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    field id-o : {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
               → 2-Hom (f ∙ refl) f

open Unit-o ⦃ ... ⦄ public

{-# DISPLAY Unit-o.id-o _ f = id-o f #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Unit-oω : Typeω
  Unit-oω = ∀{ℓx ℓy} → Unit-o C C₂ ℓx ℓy
