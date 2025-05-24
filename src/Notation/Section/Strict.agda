{-# OPTIONS --safe #-}
module Notation.Section.Strict where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Section
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) where

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄ where
    _section-of_ : {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) (r : Hom y x) → Type (ℓ-hom ℓx ℓx)
    s section-of r = Weak-section C Strict s r
    {-# NOINLINE _section-of_ #-}

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄ where
    Split-epi : {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
    Split-epi = Weak-split-epi C Strict

{-# DISPLAY Weak-split-epi {_} {_} {_} _ Strict {_} {_} ⦃ _ ⦄ ⦃ _ ⦄ {_} {_} s = Split-epi s #-}
