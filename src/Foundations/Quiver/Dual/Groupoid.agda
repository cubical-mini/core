{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} where instance

  Dual-Refl : ⦃ r : Reflω C ⦄ → Reflω (C ᵒᵖ)
  Dual-Refl ⦃ r ⦄ .refl = r .Refl.refl

  Dual-Sym : ⦃ s : Symω C ⦄ → Symω (C ᵒᵖ)
  Dual-Sym ⦃ s ⦄ .sym = s .Sym.sym

  Dual-HComp : ⦃ _ : HCompω C ⦄ → HCompω (C ᵒᵖ)
  Dual-HComp ._∙_ p q = q ∙ p


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {m′ ℓ-obᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Dual-Reflᵈ : ⦃ _ : Reflω C ⦄ ⦃ r′ : Reflωᵈ D ⦄ → Reflωᵈ (D ᵒᵖᵈ)
  Dual-Reflᵈ ⦃ r′ ⦄ .reflᵈ = r′ .Reflᵈ.reflᵈ

  Dual-Symᵈ : ⦃ _ : Symω C ⦄ ⦃ s′ : Symωᵈ D ⦄ → Symωᵈ (D ᵒᵖᵈ)
  Dual-Symᵈ ⦃ s′ ⦄ .symᵈ = s′ .Symᵈ.symᵈ

  Dual-HCompᵈ : ⦃ _ : HCompω C ⦄ ⦃ _ : HCompωᵈ D ⦄ → HCompωᵈ (D ᵒᵖᵈ)
  Dual-HCompᵈ ._∙ᵈ_ p q = q ∙ᵈ p
