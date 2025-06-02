{-# OPTIONS --safe #-}
module Notation.Composition where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where

  record Comp ℓx ℓy ℓz : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-ob ℓz l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓz l⊔ ℓ-hom ℓx ℓz) where
    no-eta-equality
    infixl 90 _∙_
    field
      _∙_ : {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
          → Hom x y → Hom y z → Hom x z

  Compω : Typeω
  Compω = ∀{ℓx ℓy ℓz} → Comp ℓx ℓy ℓz

open Comp ⦃ ... ⦄ public

{-# DISPLAY Comp._∙_ _ f g = f ∙ g #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C  : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  where
  Comp₂ : (ℓx ℓy : Level) → Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy)
  Comp₂ ℓx ℓy = {x : Ob ℓx} {y : Ob ℓy} → Comp (Quiver₂ x y) ℓx ℓx ℓx

  Compω₂ : Typeω
  Compω₂ = ∀{ℓx ℓy} → Comp₂ ℓx ℓy
