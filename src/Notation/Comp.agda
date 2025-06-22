{-# OPTIONS --safe #-}
module Notation.Comp where

open import Notation.Base

open import Notation.Base
open import Notation.Comp.Base public
open import Notation.Total
open import Notation.Wide

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  {C : Quiverω n ℓ-obω ℓ-homω} (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : Levels n → ℓ-sig m} {ℓ-homωᵈ : Levels n → Levels n → ℓ-sig² m}
  {D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ} (open Quiverωᵈ D)
  ⦃ _ : Compω C ⦄ ⦃ _ : Compωᵈ C D ⦄
  where instance

  ∫-Comp : Compω (∫ D)
  ∫-Comp ._∙_ p q .hom = p .hom ∙ q .hom
  ∫-Comp ._∙_ p q .preserves = p .preserves ∙ᵈ q .preserves

  Wide-Comp : {lsᵈ : Levels m} {t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ] lsᵈ} → Compω (Wide D lsᵈ t)
  Wide-Comp ._∙_ p q .hom = p .hom ∙ q .hom
  Wide-Comp ._∙_ p q .preserves = p .preserves ∙ᵈ q .preserves

  -- TODO need Hom [ refl ∙ refl ] x y →  Hom [ refl ] x y
  -- Component-Comp : {ls : Levels n} {t : Ob ls} {lsᵈ : Levels m} ⦃ _ : Reflω C ⦄ → Compω (Component D t lsᵈ)
  -- Component-Comp ._∙_ p q = ?

{-# INCOHERENT ∫-Comp Wide-Comp #-} -- TODO check if it's necessary

-- TODO Disp⁺ Disp⁻ Disp±
