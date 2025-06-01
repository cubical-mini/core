{-# OPTIONS --safe #-}
module Notation.Retract where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Reflexivity
open import Notation.Idempotent
open import Notation.Invertibility.Retraction
open import Notation.Reasoning.Semicategory
open import Notation.Reasoning.Category
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Path.Interface

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  _Retract-of_ = _↣!_

  Retracts : Quiver-on Ob _
  Retracts .Quiver-on.Hom = _Retract-of_

  module Retract-quiver where instance
    Retract-Refl : ⦃ _ : {ℓ : Level} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄ → Reflω Retracts
    Retract-Refl .refl .hom       = refl
    Retract-Refl .refl .preserves = reflᵈ
    {-# INCOHERENT Retract-Refl #-}

    module _  ⦃ _ : ∀{ℓw ℓx ℓy ℓz} → Assoc C Strict ℓw ℓx ℓy ℓz ⦄ ⦃ _ : ∀{ℓx ℓy} → Unit-o C Strict ℓx ℓy ⦄ where instance
      open Path-gpd
      open Path-gpd0
      Retract-Comp : Compω Retracts
      Retract-Comp ._∙_ f g .hom = f .hom ∙ g .hom
      Retract-Comp ._∙_ f g .preserves .retraction = g .preserves .retraction ∙ f .preserves .retraction
      Retract-Comp ._∙_ f g .preserves .retraction-cell
        = centralize
        ∙ collapse (g .preserves .retraction-cell)
        ∙ f .preserves .retraction-cell
      {-# INCOHERENT Retract-Comp #-}
