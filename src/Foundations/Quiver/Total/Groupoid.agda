{-# OPTIONS --safe #-}
module Foundations.Quiver.Total.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base

open import Notation.Comp.Homo
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  {D : HQuiver-onωᵈ Ob Hom m′ Ob[_] ℓ-homᵈ} where instance

  ∫-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ → Reflω (∫ C D)
  ∫-Refl .refl .fst = refl
  ∫-Refl .refl .snd = reflᵈ _ _

  ∫-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄ → Symω (∫ C D)
  ∫-Sym .sym p .fst = sym (p .fst)
  ∫-Sym .sym p .snd = symᵈ (p .snd)

  ∫-Comp : ⦃ _ : HCompω C ⦄ ⦃ _ : HCompωᵈ C D ⦄ → HCompω (∫ C D)
  ∫-Comp ._∙_ p q .fst = p .fst ∙ q .fst
  ∫-Comp ._∙_ p q .snd = p .snd ∙ᵈ q .snd

{-# INCOHERENT ∫-Refl ∫-Sym ∫-Comp #-}
