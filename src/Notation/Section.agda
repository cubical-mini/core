{-# OPTIONS --safe #-}
module Notation.Section where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (CC : 2-Quiver-on C) (open 2-Quiver-on CC) where

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄ where
    Weak-section : {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) (r : Hom y x) → Type (ℓ-hom ℓx ℓx)
    Weak-section s r = 2-Hom (s ∙ r) refl

  module _ {ℓx ℓy : Level} ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄ where
    record Weak-split-epi {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) : Type (ℓ-hom ℓy ℓy l⊔ ℓ-hom ℓy ℓx) where
      no-eta-equality
      field
        section      : Hom y x
        section-cell : Weak-section section r
