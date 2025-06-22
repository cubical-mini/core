{-# OPTIONS --safe #-}
module Notation.Sym where

open import Notation.Base
open import Notation.Sym.Base public
open import Notation.Total
open import Notation.Wide

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  {C : Quiverω n ℓ-obω ℓ-homω} (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : Levels n → ℓ-sig m} {ℓ-homωᵈ : Levels n → Levels n → ℓ-sig² m}
  {D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ} (open Quiverωᵈ D)
  ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄
  where instance

  ∫-Sym : Symω (∫ D)
  ∫-Sym .sym p .hom = sym (p .hom)
  ∫-Sym .sym p .preserves = symᵈ (p .preserves)

  Wide-Sym : {lsᵈ : Levels m} {t : ∀{ℓ} {x : Ob ℓ} → Ob[ x ] lsᵈ} → Symω (Wide D lsᵈ t)
  Wide-Sym .sym p .hom = sym (p .hom)
  Wide-Sym .sym p .preserves = symᵈ (p .preserves)

  -- TODO need Hom [ sym refl ] x y →  Hom [ refl ] x y
  -- Component-Sym : {ls : Levels n} {t : Ob ls} {lsᵈ : Levels m} ⦃ _ : Reflω C ⦄ → Symω (Component D t lsᵈ)
  -- Component-Sym .sym p = {!!}

{-# INCOHERENT ∫-Sym Wide-Sym #-} -- TODO check if it's necessary

-- TODO Disp⁺ Disp⁻ Disp±
