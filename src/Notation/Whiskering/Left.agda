{-# OPTIONS --safe #-}
module Notation.Whiskering.Left where

open import Prim.Type

open import Notation.Base
open import Notation.Composition

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  (ℓx ℓy ℓz : Level) ⦃ _ : Comp C ℓx ℓy ℓz ⦄ where

  record Whisker-l : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-ob ℓz l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓx ℓz l⊔ ℓ-hom ℓy ℓz) where
    no-eta-equality
    infixr 24 _◁_
    field _◁_ : {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
                {z : Ob ℓz} {g h : Hom y z} (α : 2-Hom g h)
              → 2-Hom (f ∙ g) (f ∙ h)

open Whisker-l ⦃ ... ⦄ public

{-# DISPLAY Whisker-l._◁_ _ f α = f ◁ α #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Compω C ⦄ where

  Whisker-lω : Typeω
  Whisker-lω = ∀{ℓx ℓy ℓz} → Whisker-l C C₂ ℓx ℓy ℓz
