{-# OPTIONS --safe #-}
module Notation.Duality where

open import Prim.Kan
open import Prim.Type

open import Notation.Quiver
open import Notation.Symmetry


module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) ⦃ _ : Symmetry Ob Hom ⦄
  (_~_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)) where

  record Dual : Typeω where
    no-eta-equality
    field invol : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f : Hom x y)
                → sym (sym f) ~ f

    infixl 60 _ᵒᵖ
    _ᵒᵖ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Hom y x
    _ᵒᵖ = sym
    {-# NOINLINE _ᵒᵖ #-}

open Dual ⦃ ... ⦄ public

{-# DISPLAY Dual.invol _ f g h = invol f g h #-}
