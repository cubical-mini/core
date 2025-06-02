{-# OPTIONS --safe #-}
module Notation.Terminal where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Symmetry
open import Notation.Terminal.Base public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  {ℓt ℓ : Level} ⦃ _ : Weak-Terminal C C₂ ℓt ℓ ⦄ where

  module _ ⦃ _ : Symmetryω₂ C C₂ ⦄ where
    !-unique : {x : Ob ℓ} (h : Hom x ⊤) → 2-Hom h !
    !-unique h = sym (!-cell h)

    module _ ⦃ _ : Compω₂ C C₂ ⦄ where
      !-unique² : {x : Ob ℓ} (f g : Hom x ⊤) → 2-Hom f g
      !-unique² f g = sym (!-cell f) ∙ !-cell g
