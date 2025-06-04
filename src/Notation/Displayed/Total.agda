{-# OPTIONS --safe #-}
module Notation.Displayed.Total where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Composition
open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Symmetry
open import Notation.Displayed.Total.Base public
open import Notation.Reflexivity
open import Notation.Symmetry

module Total-gpd where
  module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C)
    {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} {D : Quiver-onᵈ C Ob[_] ℓ-homᵈ} (open Quiver-onᵈ D) where instance
    Total-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflᵈω C D ⦄ → Reflω (∫ D)
    Total-Refl .refl .hom = refl
    Total-Refl .refl .preserves = reflᵈ

    Total-Sym : ⦃ _ : Symmetryω C ⦄ ⦃ _ : Symmetryᵈω C D ⦄ → Symmetryω (∫ D)
    Total-Sym .sym f .hom = sym (f .hom)
    Total-Sym .sym f .preserves = symᵈ (f .preserves)

    Total-Comp : ⦃ _ : Compω C ⦄ ⦃ _ : Compᵈω C D ⦄ → Compω (∫ D)
    Total-Comp ._∙_ f g .hom = f .hom ∙ g. hom
    Total-Comp ._∙_ f g .preserves = f .preserves ∙ᵈ g .preserves
    {-# OVERLAPPING Total-Refl Total-Sym Total-Comp #-}
