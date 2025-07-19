{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Groupoid
open import Foundations.Quiver.Wide.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob ℓ-het} {Ob : ob-sig ℓ-ob} {C : HQuiver-onω m Ob ℓ-het}
  {ℓ-homᵈ} {D : Quiver-onωᵈ Ob Ob _ 0 0 (λ _ _ → ⊤) (λ _ _ → ⊤) ℓ-homᵈ} where instance

  Wide-Refl : ⦃ _ : Reflω C ⦄ ⦃ _ : Reflωᵈ C D ⦄ → Reflω (Wide C D)
  Wide-Refl .refl .fst = refl
  Wide-Refl .refl .snd = reflᵈ _

  Wide-Sym : ⦃ _ : Symω C ⦄ ⦃ _ : Symωᵈ C D ⦄ → Symω (Wide C D)
  Wide-Sym .sym p .fst = sym  (p .fst)
  Wide-Sym .sym p .snd = symᵈ (p .snd)

  Wide-HComp : ⦃ _ : HCompω C ⦄ ⦃ _ : HCompωᵈ C D ⦄ → HCompω (Wide C D)
  Wide-HComp ._∙_ p q .fst = p .fst ∙ q .fst
  Wide-HComp ._∙_ p q .snd = p .snd ∙ᵈ q .snd

{-# INCOHERENT Wide-Refl Wide-Sym Wide-HComp #-}
