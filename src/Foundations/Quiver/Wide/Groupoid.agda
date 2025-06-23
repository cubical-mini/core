{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Wide.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {n ℓ-ob ℓ-hom} {C : Quiverω n ℓ-ob ℓ-hom} (open Quiverω C)
  {ℓ-homᵈ} {D : Quiver-onωᵈ Ob Hom 0 (λ _ _ → ⊤) ℓ-homᵈ} where instance

  Wide-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C (Wideᵈ C D) ⦄ → Reflω (Wide C D)
  Wide-Refl .refl .hom = refl
  Wide-Refl .refl .preserves = reflᵈ _

  Wide-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C (Wideᵈ C D) ⦄ → Symω (Wide C D)
  Wide-Sym .sym p .hom = sym (p .hom)
  Wide-Sym .sym p .preserves = symᵈ (p .preserves)

  Wide-Comp : ⦃ _ : Compω C ⦄ ⦃ _ : Compωᵈ C (Wideᵈ C D) ⦄ → Compω (Wide C D)
  Wide-Comp ._∙_ p q .hom = p .hom ∙ q .hom
  Wide-Comp ._∙_ p q .preserves = p .preserves ∙ᵈ q .preserves

{-# INCOHERENT Wide-Refl Wide-Sym Wide-Comp #-}
