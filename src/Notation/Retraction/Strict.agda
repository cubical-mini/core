{-# OPTIONS --safe #-}
module Notation.Retraction.Strict where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Retraction
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) where

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄ where
    _retraction-of_ : {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) (s : Hom y x) → Type (ℓ-hom ℓy ℓy)
    r retraction-of s = Weak-retraction C Strict r s
    {-# NOINLINE _retraction-of_ #-}

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄ where
    Split-mono : {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx)
    Split-mono = Weak-split-mono C Strict

{-# DISPLAY Weak-split-mono {_} {_} {_} _ Strict {_} {_} ⦃ _ ⦄ ⦃ _ ⦄ {_} {_} s = Split-mono s #-}
