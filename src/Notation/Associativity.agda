{-# OPTIONS --safe #-}
module Notation.Associativity where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC)
  (ℓw ℓx ℓy ℓz : Level) ⦃ _ : Comp C ℓw ℓx ℓz ⦄ ⦃ _ : Comp C ℓx ℓy ℓz ⦄ ⦃ _ : Comp C ℓw ℓx ℓy ⦄ ⦃ _ : Comp C ℓw ℓy ℓz ⦄ where

  record Assoc : Type (ℓ-ob ℓw l⊔ ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-ob ℓz l⊔ ℓ-hom ℓw ℓx l⊔ ℓ-hom ℓw ℓz l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓz) where
    no-eta-equality
    field assoc : {w : Ob ℓw} {x : Ob ℓx} (f : Hom w x) {y : Ob ℓy} (g : Hom x y) {z : Ob ℓz} (h : Hom y z)
                → 2-Hom (f ∙ (g ∙ h)) ((f ∙ g) ∙ h)

open Assoc ⦃ ... ⦄ public

{-# DISPLAY Assoc.assoc _ f g h = assoc f g h #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Compω C ⦄ where

  Assocω : Typeω
  Assocω = ∀{ℓw ℓx ℓy ℓz} → Assoc C C₂ ℓw ℓx ℓy ℓz


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Compω C ⦄ where instance

  Assoc⁻ : ⦃ A : Assocω C Strict ⦄ → Assocω C (Strict ²ᵒᵖω)
  Assoc⁻ ⦃ A ⦄ .assoc f g h i = A .Assoc.assoc f g h (~ i)
  {-# INCOHERENT Assoc⁻ #-}
