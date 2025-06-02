{-# OPTIONS --safe #-}
module Notation.Whiskering.Right where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC)
  (ℓx ℓy ℓz : Level) ⦃ _ : Comp C ℓx ℓy ℓz ⦄ where

  record Whisker-r : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-ob ℓz l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓx ℓz l⊔ ℓ-hom ℓy ℓz) where
    no-eta-equality
    infixr 24 _▷_
    field _▷_ : {x : Ob ℓx} {y : Ob ℓy}
                {f g : Hom x y} (α : 2-Hom f g)
                {z : Ob ℓz} (h : Hom y z)
              → 2-Hom (f ∙ h) (g ∙ h)

open Whisker-r ⦃ ... ⦄ public

{-# DISPLAY Whisker-r._▷_ _ α h = α ▷ h #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Compω C ⦄ where

  Whisker-rω : Typeω
  Whisker-rω = ∀{ℓx ℓy ℓz} → Whisker-r C C₂ ℓx ℓy ℓz


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy ℓz : Level} ⦃ _ : Comp C ℓx ℓy ℓz ⦄ where instance

  Strict-Whisker-r : Whisker-r C Strict ℓx ℓy ℓz
  Strict-Whisker-r ._▷_ p h i = p i ∙ h
  {-# OVERLAPPING Strict-Whisker-r #-}
