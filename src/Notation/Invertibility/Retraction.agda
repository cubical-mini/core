{-# OPTIONS --safe #-}
module Notation.Invertibility.Retraction where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Composition
open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Wide
open import Notation.Idempotent
open import Notation.Reasoning.Category
open import Notation.Reasoning.Semicategory
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Outer
open import Notation.Whiskering.Right

open import Notation.Invertibility.Retraction.Base public

open import Foundations.Path.Interface

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Split-monosᵈ : Quiver-onᵈ C (λ _ → ⊤) (λ ℓx ℓy → ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓy ℓx)
  Split-monosᵈ .Quiver-onᵈ.Hom[_] f _ _ = Split-mono f

  infix 10 _↣!_
  _↣!_ : ∀ {ℓx ℓy}(y : Ob ℓy) (x : Ob ℓx) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓy)
  y ↣! x = Total-hom C Split-monosᵈ {x = y} {y = x} tt tt

  _Retract-of_ = _↣!_

  Retracts : Quiver-on Ob _
  Retracts = Wide Split-monosᵈ

  open Path-gpd
  open Path-gpd0
  instance
    Split-mono-reflᵈ : ⦃ _ : ∀{ℓ} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄
                     → Reflᵈω C Split-monosᵈ
    Split-mono-reflᵈ .reflᵈ .retraction      = refl
    Split-mono-reflᵈ .reflᵈ .retraction-cell = idem

    Split-mono-compᵈ : ⦃ _ : Assocω C Strict ⦄ ⦃ _ : Unit-oω C Strict ⦄ → Compᵈω C Split-monosᵈ
    Split-mono-compᵈ ._∙ᵈ_ f′ g′ .retraction = g′ .retraction ∙ f′ .retraction
    Split-mono-compᵈ ._∙ᵈ_ f′ g′ .retraction-cell
      = centralize ∙ (collapse (g′ .retraction-cell) ∙ f′ .retraction-cell)

{-# DISPLAY Total-hom {_} {_} {_} _ {_} {_} {_} Split-monosᵈ {_} {_} {x} {y} _ _ = x ↣! y #-}
