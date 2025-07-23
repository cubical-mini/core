{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Groupoid
open import Foundations.Quiver.Wide.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} ℓ-hom {C : HQuiver-onω m Ob ℓ-hom}
  {ℓ-homᵈ} {D : HQuiver-onωᵈ C 0 (λ _ _ → ⊤) ℓ-homᵈ} where instance

  Wide-Refl : ⦃ _ : Refl C ⦄ ⦃ _ : Reflᵈ D ⦄ → Refl (Wide D)
  Wide-Refl .refl .fst = refl
  Wide-Refl .refl .snd = reflᵈ

  Wide-Sym : ⦃ _ : Sym C ⦄ ⦃ _ : Symᵈ D ⦄ → Sym (Wide D)
  Wide-Sym .sym p .fst = sym  (p .fst)
  Wide-Sym .sym p .snd = symᵈ (p .snd)

  Wide-HComp : ⦃ _ : HComp C ⦄ ⦃ _ : HCompᵈ D ⦄ → HComp (Wide D)
  Wide-HComp ._∙_ p q .fst = p .fst ∙ q .fst
  Wide-HComp ._∙_ p q .snd = p .snd ∙ᵈ q .snd

{-# INCOHERENT Wide-Refl Wide-Sym Wide-HComp #-}
