{-# OPTIONS --safe #-}
module Notation.Symmetry where

open import Prim.Type

open import Notation.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where

  record Symmetry ℓx ℓy : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx) where
    no-eta-equality
    field sym : {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Hom y x

  Symmetryω : Typeω
  Symmetryω = ∀{ℓx ℓy} → Symmetry ℓx ℓy

open Symmetry ⦃ ... ⦄ public

{-# DISPLAY Symmetry.sym _ f = sym f #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C  : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  where
  Symmetry₂ : (ℓx ℓy : Level) → Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy)
  Symmetry₂ ℓx ℓy = {x : Ob ℓx} {y : Ob ℓy} → Symmetry (Quiver₂ x y) ℓx ℓx

  Symmetryω₂ : Typeω
  Symmetryω₂ = ∀{ℓx ℓy} → Symmetry₂ ℓx ℓy
