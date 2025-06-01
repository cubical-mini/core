{-# OPTIONS --safe #-}
module Notation.Invertibility.Quasi where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Invertibility.Retraction
open import Notation.Invertibility.Section
open import Notation.Reflexivity
open import Notation.Split

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  {ℓx ℓy : Level}
  ⦃ _ : Refl C ℓx ⦄ ⦃ _ : Comp C ℓx ℓy ℓx ⦄
  ⦃ _ : Refl C ℓy ⦄ ⦃ _ : Comp C ℓy ℓx ℓy ⦄
  where

  record Quasi-inverse {x : Ob ℓx} {y : Ob ℓy} (to : Hom x y)
    : Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓy) where
    constructor mk-quasi-inverse
    no-eta-equality
    field
      from    : Hom y x
      to-from : from retraction-of to
      from-to : from section-of    to

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Quasi-inversesᵈ : Quiver-onᵈ C (λ _ → ⊤) (λ ℓx ℓy → ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  Quasi-inversesᵈ .Quiver-onᵈ.Hom[_] f _ _ = Quasi-inverse f

  infix 10 _≅_
  _≅_ : ∀ {ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  x ≅ y = Total-hom C Quasi-inversesᵈ {x = x} {y = y} tt tt

{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} Quasi-inversesᵈ {_} {_} {x} {y} _ _ = x ≅ y #-}
