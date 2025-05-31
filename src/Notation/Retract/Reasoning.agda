{-# OPTIONS --safe #-}
module Notation.Retract.Reasoning where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Idempotent
open import Notation.Reasoning
open import Notation.Reflexivity
open import Notation.Retract
open import Notation.Strict
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Left.Strict
open import Notation.Whiskering.Right
open import Notation.Whiskering.Right.Strict

open import Foundations.Path.Interface

-- TODO levels?
module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Retracts : Quiver-on Ob _
  Retracts .Quiver-on.Hom = _Retract-of_

  instance
    Retract-Refl : ⦃ _ : {ℓ : Level} {x : Ob ℓ} → Idem C Strict {x = x} refl ⦄ → Reflω Retracts
    Retract-Refl .refl ._Retract-of_.to = refl
    Retract-Refl .refl ._Retract-of_.from = refl
    Retract-Refl .refl ._Retract-of_.retract-cell = idem

  module _ {ℓx ℓy ℓz : Level} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz} (f : x Retract-of y) (g : y Retract-of z)
    ⦃ _ : Assoc C Strict ℓx ℓy ℓz ℓy ⦄ ⦃ _ : Assoc C Strict ℓx ℓz ℓy ℓx ⦄ ⦃ _ : Unit-o C Strict ℓx ℓy ⦄ where
    open _Retract-of_ f renaming (to to f⁺; from to f⁻; retract-cell to f⁺f⁻)
    open _Retract-of_ g renaming (to to g⁺; from to g⁻; retract-cell to g⁺g⁻)

    _∙ᵣ_ : x Retract-of z
    _∙ᵣ_ ._Retract-of_.to   = f⁺ ∙ g⁺
    _∙ᵣ_ ._Retract-of_.from = g⁻ ∙ f⁻
    _∙ᵣ_ ._Retract-of_.retract-cell =
      (f⁺ ∙ g⁺) ∙ (g⁻ ∙ f⁻)  ~⟨ assoc (f⁺ ∙ g⁺) g⁻ f⁻ ⟩
      f⁺ ∙ g⁺ ∙ g⁻ ∙ f⁻      ~⟨ assoc f⁺ g⁺ g⁻ ▷ f⁻ ⟨
      f⁺ ∙ (g⁺ ∙ g⁻) ∙ f⁻    ~⟨ (f⁺ ◁ g⁺g⁻) ▷ f⁻ ⟩
      f⁺ ∙ refl ∙ f⁻         ~⟨ id-o f⁺ ▷ f⁻ ⟩
      f⁺ ∙ f⁻                ~⟨ f⁺f⁻ ⟩
      refl                   ∎

  module _ ⦃ _ : ∀{ℓw ℓx ℓy ℓz} → Assoc C Strict ℓw ℓx ℓy ℓz ⦄ ⦃ _ : ∀{ℓx ℓy} → Unit-o C Strict ℓx ℓy ⦄ where instance
    Retract-Comp : Compω Retracts
    Retract-Comp ._∙_ f g = f ∙ᵣ g

{-# INCOHERENT Retract-Refl Retract-Comp #-}
