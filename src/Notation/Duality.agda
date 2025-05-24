{-# OPTIONS --safe #-}
module Notation.Duality where

open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Symmetry

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC)
  (ℓx ℓy : Level) ⦃ _ : Symmetry C ℓx ℓy ⦄ ⦃ _ : Symmetry C ℓy ℓx ⦄ where

  record Dual : Type (ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    field invol : {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
                → 2-Hom (sym (sym f)) f

    infixl 60 _ᵒᵖ
    _ᵒᵖ : {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Hom y x
    _ᵒᵖ = sym
    {-# NOINLINE _ᵒᵖ #-}

open Dual ⦃ ... ⦄ public

{-# DISPLAY Dual.invol _ f g h = invol f g h #-}
