{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {m ℓ-obᵈ ℓ-homᵈ} {D : Quiverωᵈ C m ℓ-obᵈ ℓ-homᵈ} (open Quiverωᵈ D)
  where instance

  ∫-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ → Reflω (∫ D)
  ∫-Refl .refl .hom = refl
  ∫-Refl .refl .preserves = reflᵈ _

  ∫-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄ → Symω (∫ D)
  ∫-Sym .sym p .hom = sym (p .hom)
  ∫-Sym .sym p .preserves = symᵈ (p .preserves)

  ∫-Comp : ⦃ _ : Compω C ⦄ ⦃ _ : Compωᵈ C D ⦄ → Compω (∫ D)
  ∫-Comp ._∙_ p q .hom = p .hom ∙ q .hom
  ∫-Comp ._∙_ p q .preserves = p .preserves ∙ᵈ q .preserves

{-# INCOHERENT ∫-Refl ∫-Sym ∫-Comp #-}
