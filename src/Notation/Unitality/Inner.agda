{-# OPTIONS --safe #-}
module Notation.Unitality.Inner where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  (ℓx ℓy : Level) ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓx ℓy ⦄ where

  record Unit-i : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    field id-i : {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
               → 2-Hom (refl ∙ f) f

open Unit-i ⦃ ... ⦄ public

{-# DISPLAY Unit-i.id-i _ f = id-i f #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Unit-iω : Typeω
  Unit-iω = ∀{ℓx ℓy} → Unit-i C C₂ ℓx ℓy
