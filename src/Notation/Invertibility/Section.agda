{-# OPTIONS --safe #-}
module Notation.Invertibility.Section where

open import Prim.Data.Unit
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level} ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄ where

  record Split-epi {x : Ob ℓx} {y : Ob ℓy} (r : Hom y x) : Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy) where
    no-eta-equality
    field
      section      : Hom x y
      section-cell : section section-of r

open Split-epi public

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split-episᵈ : Quiver-onᵈ C (λ _ → ⊤) _
  Split-episᵈ .Quiver-onᵈ.Hom[_] f _ _ = Split-epi f

  infix 10 _↠!_
  _↠!_ : ∀ {ℓx ℓy} (y : Ob ℓy) (x : Ob ℓx) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓx ℓx)
  y ↠! x = Total-hom C Split-episᵈ {x = y} {y = x} tt tt

{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} Split-episᵈ {_} {_} {x} {y} _ _ = x ↠! y #-}
