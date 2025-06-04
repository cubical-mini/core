{-# OPTIONS --safe #-}
module Notation.Displayed.Wide where

open import Prim.Data.Unit
open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Composition
open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Symmetry
open import Notation.Displayed.Total
open import Notation.Displayed.Wide.Base public
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Symmetry

module Wide-gpd where
  module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
    {ℓ-homᵈ : ℓ-hom-sig} {D : Quiver-onᵈ C (λ {_} _ → ⊤) ℓ-homᵈ} (open Quiver-onᵈ D) where instance
    Wide-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflᵈω C D ⦄ → Reflω (Wide D)
    Wide-Refl .refl .hom = refl
    Wide-Refl .refl .preserves = reflᵈ

    Wide-Sym : ⦃ _ : Symmetryω C ⦄ ⦃ _ : Symmetryᵈω C D ⦄ → Symmetryω (Wide D)
    Wide-Sym .sym f .hom = sym (f .hom)
    Wide-Sym .sym f .preserves = symᵈ (f .preserves)

    Wide-Comp : ⦃ _ : Compω C ⦄ ⦃ _ : Compᵈω C D ⦄ → Compω (Wide D)
    Wide-Comp ._∙_ f g .hom = f .hom ∙ g. hom
    Wide-Comp ._∙_ f g .preserves = f .preserves ∙ᵈ g .preserves
    {-# INCOHERENT Wide-Refl Wide-Sym Wide-Comp #-}
