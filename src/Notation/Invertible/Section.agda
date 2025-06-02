{-# OPTIONS --safe #-}
module Notation.Invertible.Section where

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
open import Notation.Invertible.Section.Base public
open import Notation.Reasoning.Category
open import Notation.Reasoning.Semicategory
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where

  Weak-split-episᵈ : Quiver-onᵈ C (λ _ → ⊤) _
  Weak-split-episᵈ .Quiver-onᵈ.Hom[_] f _ _ = Weak-split-epi C C₂ f

  Weak-split-epis : Quiver-on Ob _
  Weak-split-epis = Wide Weak-split-episᵈ


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where instance

  Weak-split-epi-Reflᵈ : ⦃ _ : ∀{ℓ} {x : Ob ℓ} → Weak-Idem C C₂ {x = x} refl ⦄
                       → Reflᵈω C (Weak-split-episᵈ C C₂)
  Weak-split-epi-Reflᵈ .reflᵈ .section      = refl
  Weak-split-epi-Reflᵈ .reflᵈ .section-cell = idem

  Weak-split-epi-Compᵈ : ⦃ _ : Assocω C C₂ ⦄ ⦃ _ : Unit-oω C C₂ ⦄
                         ⦃ _ : Symmetryω₂ C C₂ ⦄ ⦃ _ : Compω₂ C C₂ ⦄ ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
                  → Compᵈω C (Weak-split-episᵈ C C₂)
  Weak-split-epi-Compᵈ ._∙ᵈ_ f′ g′ .section = g′ .section ∙ f′ .section
  Weak-split-epi-Compᵈ ._∙ᵈ_ f′ g′ .section-cell = centralize ∙ collapse-l (f′ .section-cell) ∙ g′ .section-cell
  {-# OVERLAPPING Weak-split-epi-Reflᵈ Weak-split-epi-Compᵈ #-}
