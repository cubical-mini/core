{-# OPTIONS --safe #-}
module Notation.Invertible.Retraction where

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
open import Notation.Invertible.Retraction.Base
  public
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

  Weak-split-monosᵈ : Quiver-onᵈ C (λ _ → ⊤) _
  Weak-split-monosᵈ .Quiver-onᵈ.Hom[_] f _ _ = Weak-split-mono C C₂ f

  Weak-retract : ∀ {ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Type (ℓ-hom ℓx ℓx l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓx)
  Weak-retract x y = Total-hom C Weak-split-monosᵈ {x = x} {y = y} tt tt

  Weak-split-monos : Quiver-on Ob _
  Weak-split-monos = Wide Weak-split-monosᵈ


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) {C₂ : 2-Quiver-on C} (open 2-Quiver-on C₂)
  ⦃ _ : Reflω C ⦄ ⦃ _ : Compω C ⦄ where instance

  Weak-split-mono-Reflᵈ : ⦃ _ : ∀{ℓ} {x : Ob ℓ} → Weak-Idem C C₂ {x = x} refl ⦄
                        → Reflᵈω C (Weak-split-monosᵈ C C₂)
  Weak-split-mono-Reflᵈ .reflᵈ .retraction      = refl
  Weak-split-mono-Reflᵈ .reflᵈ .retraction-cell = idem

  Weak-split-mono-Compᵈ : ⦃ _ : Assocω C C₂ ⦄ ⦃ _ :  Unit-oω C C₂ ⦄
                          ⦃ _ : Symmetryω₂ C C₂ ⦄ ⦃ _ : Compω₂ C C₂ ⦄ ⦃ _ : Whisker-lω C C₂ ⦄ ⦃ _ : Whisker-rω C C₂ ⦄
                        → Compᵈω C (Weak-split-monosᵈ C C₂)
  Weak-split-mono-Compᵈ ._∙ᵈ_ f′ g′ .retraction = g′ .retraction ∙ f′ .retraction
  Weak-split-mono-Compᵈ ._∙ᵈ_ f′ g′ .retraction-cell = centralize ∙ collapse-l (g′ .retraction-cell) ∙ f′ .retraction-cell
  {-# OVERLAPPING Weak-split-mono-Reflᵈ Weak-split-mono-Compᵈ #-}
