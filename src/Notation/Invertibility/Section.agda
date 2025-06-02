{-# OPTIONS --safe #-}
module Notation.Invertibility.Section where

open import Prim.Data.Unit
open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Composition
open import Notation.Displayed.Reflexivity
open import Notation.Idempotent
open import Notation.Reasoning.Category
open import Notation.Reasoning.Semicategory
open import Notation.Reflexivity
open import Notation.Split
open import Notation.Strict
open import Notation.Unitality.Outer
open import Notation.Whiskering.Right

open import Notation.Invertibility.Section.Base public

open import Foundations.Path.Interface

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split-episᵈ : Quiver-onᵈ C (λ _ → ⊤) _
  Split-episᵈ .Quiver-onᵈ.Hom[_] f _ _ = Split-epi f

  infix 10 _↠!_
  _↠!_ : ∀ {ℓx ℓy} (y : Ob ℓy) (x : Ob ℓx) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓx ℓx)
  y ↠! x = Total-hom C Split-episᵈ {x = y} {y = x} tt tt

  open Path-gpd
  open Path-gpd0
  instance
    Split-epi-reflᵈ : ⦃ _ : ∀{ℓ} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄
                    → Reflᵈω C Split-episᵈ
    Split-epi-reflᵈ .reflᵈ .section      = refl
    Split-epi-reflᵈ .reflᵈ .section-cell = idem

    Split-epi-compᵈ : ⦃ _ : Assocω C Strict ⦄ ⦃ _ : Unit-oω C Strict ⦄ → Compᵈω C Split-episᵈ
    Split-epi-compᵈ ._∙ᵈ_ f′ g′ .section = g′ .section ∙ f′ .section
    Split-epi-compᵈ ._∙ᵈ_ f′ g′ .section-cell
      = centralize ∙ (collapse (f′ .section-cell) ∙ g′ .section-cell)

{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} Split-episᵈ {_} {_} {x} {y} _ _ = x ↠! y #-}
