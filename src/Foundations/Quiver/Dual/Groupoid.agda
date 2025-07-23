{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} where instance

  Dual-Refl : ⦃ r : Refl C ⦄ → Refl (C ᵒᵖ)
  Dual-Refl ⦃ r ⦄ .refl = r .Refl.refl

  Dual-Sym : ⦃ s : Sym C ⦄ → Sym (C ᵒᵖ)
  Dual-Sym ⦃ s ⦄ .sym = s .Sym.sym

  Dual-HComp : ⦃ _ : HComp C ⦄ → HComp (C ᵒᵖ)
  Dual-HComp ._∙_ p q = q ∙ p


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {m′ ℓ-obᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Dual-Reflᵈ : ⦃ _ : Refl C ⦄ ⦃ r′ : Reflᵈ D ⦄ → Reflᵈ (D ᵒᵖᵈ)
  Dual-Reflᵈ ⦃ r′ ⦄ .reflᵈ = r′ .Reflᵈ.reflᵈ

  Dual-Symᵈ : ⦃ _ : Sym C ⦄ ⦃ s′ : Symᵈ D ⦄ → Symᵈ (D ᵒᵖᵈ)
  Dual-Symᵈ ⦃ s′ ⦄ .symᵈ = s′ .Symᵈ.symᵈ

  Dual-HCompᵈ : ⦃ _ : HComp C ⦄ ⦃ _ : HCompᵈ D ⦄ → HCompᵈ (D ᵒᵖᵈ)
  Dual-HCompᵈ ._∙ᵈ_ p q = q ∙ᵈ p
