{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Groupoid where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base

open import Notation.Comp
open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} where instance

  Dual-Refl : ⦃ r : Reflω C ⦄ → Reflω (Op C)
  Dual-Refl ⦃ r ⦄ .refl = r .Refl.refl

  Dual-Sym : ⦃ s : Symω C ⦄ → Symω (Op C)
  Dual-Sym ⦃ s ⦄ .sym = s .Sym.sym

  Dual-HComp : ⦃ _ : HCompω C ⦄ → HCompω (Op C)
  Dual-HComp ._∙_ p q = q ∙ p


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom)
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ Ob _ m′ Ob[_] ℓ-homᵈ) where instance

  Dual-Reflᵈ : ⦃ _ : Reflω C ⦄ ⦃ r′ : Reflωᵈ C D ⦄ → Reflωᵈ (Op C) (Opᵈ C D)
  Dual-Reflᵈ ⦃ r′ ⦄ .reflᵈ = r′ .Reflᵈ.reflᵈ

  Dual-Symᵈ : ⦃ _ : Symω C ⦄ ⦃ s′ : Symωᵈ C D ⦄ → Symωᵈ (Op C) (Opᵈ C D)
  Dual-Symᵈ ⦃ s′ ⦄ .symᵈ = s′ .Symᵈ.symᵈ

  Dual-HCompᵈ : ⦃ _ : HCompω C ⦄ ⦃ _ : HCompωᵈ C D ⦄ → HCompωᵈ (Op C) (Opᵈ C D)
  Dual-HCompᵈ ._∙ᵈ_ p q = q ∙ᵈ p
