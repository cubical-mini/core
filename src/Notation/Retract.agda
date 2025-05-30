{-# OPTIONS --safe #-}
module Notation.Retract where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Retraction.Strict
open import Notation.Section.Strict
open import Notation.Strict

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level}
  ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄ where

  -- TODO maybe weak retracts are useful too?
  record _Retract-of_ (x : Ob ℓx) (y : Ob ℓy) : Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx) where
    no-eta-equality
    field
      to           : Hom x y
      from         : Hom y x
      retract-cell : from retraction-of to

    sect-cell : to section-of from
    sect-cell = retract-cell
