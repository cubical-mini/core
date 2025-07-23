{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Σ-Refl : ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄ → Refl (Σ C D)
  Σ-Refl .refl .fst = refl
  Σ-Refl .refl .snd = reflᵈ

  Σ-Sym : ⦃ _ : Sym C ⦄ ⦃ _ : Symᵈ D ⦄ → Sym (Σ C D)
  Σ-Sym .sym p .fst = sym  (p .fst)
  Σ-Sym .sym p .snd = symᵈ (p .snd)

  Σ-HComp : ⦃ _ : HComp C ⦄ ⦃ _ : HCompᵈ D ⦄ → HComp (Σ C D)
  Σ-HComp ._∙_ p q .fst = p .fst ∙ q .fst
  Σ-HComp ._∙_ p q .snd = p .snd ∙ᵈ q .snd

{-# INCOHERENT Σ-Refl Σ-Sym Σ-HComp #-}
