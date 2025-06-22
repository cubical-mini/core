{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Wide.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  {C : Quiverω n ℓ-obω ℓ-homω} (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : Levels n → ℓ-sig m} {ℓ-homωᵈ : Levels n → Levels n → ℓ-sig² m}
  {D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ} (open Quiverωᵈ D)
  {lsᵈ : Levels m} {t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ] lsᵈ}
  where instance

  Wide-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ → Reflω (Wide D t)
  Wide-Refl .refl .hom = refl
  Wide-Refl .refl .preserves = reflᵈ _

  Wide-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄ → Symω (Wide D t)
  Wide-Sym .sym p .hom = sym (p .hom)
  Wide-Sym .sym p .preserves = symᵈ (p .preserves)

  Wide-Comp : ⦃ _ : Compω C ⦄ ⦃ _ : Compωᵈ C D ⦄ → Compω (Wide D t)
  Wide-Comp ._∙_ p q .hom = p .hom ∙ q .hom
  Wide-Comp ._∙_ p q .preserves = p .preserves ∙ᵈ q .preserves

{-# INCOHERENT Wide-Refl Wide-Sym Wide-Comp #-}
