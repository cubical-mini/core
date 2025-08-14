{-# OPTIONS --safe #-}
module Foundations.Dual.Instances where

open import Foundations.Base
open import Foundations.Discrete.Base
open import Foundations.Dual.Base
open import Foundations.Lens.Pull.Base
open import Foundations.Lens.Push.Base

open import Notation.Refl
open import Notation.Sym

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} where instance

  Dual-Refl : ⦃ r : Refl C ⦄ → Refl (C ᵒᵖ)
  Dual-Refl ⦃ r ⦄ .refl = r .Refl.refl

  Dual-Sym : ∀{ℓf} {F : ∀{lxs lys} (x : Ob lxs) (y : Ob lys) → HQuiver-onω 0 _ ℓf}
             ⦃ s : Sym C F ⦄ → Sym (C ᵒᵖ) λ x y → F y x
  Dual-Sym ⦃ s ⦄ .sym = s .Sym.sym
  Dual-Sym ⦃ s ⦄ .sym-invol = s .Sym.sym-invol


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {m′ ℓ-obᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ}
  {D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ} where instance

  Dual-Reflᵈ : ⦃ _ : Refl C ⦄ ⦃ r′ : Reflᵈ D ⦄ → Reflᵈ (D ᵒᵖᵈ)
  Dual-Reflᵈ ⦃ r′ ⦄ .reflᵈ = r′ .Reflᵈ.reflᵈ


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {k ℓ-obᶠ ℓ-obᵍ} {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-hetᶠ ls)} where instance

  Dual-Push : ⦃ _ : Refl C ⦄ ⦃ hp : Pull C k α ⦄ → Push (C ᵒᵖ) k (λ t → α t ᵒᵖ)
  Dual-Push ._▷_ u p = p ◁ u
  Dual-Push .push-refl = pull-refl

  Dual-Pull : ⦃ _ : Refl C ⦄ ⦃ pp : Push C k α ⦄ → Pull (C ᵒᵖ) k (λ t → α t ᵒᵖ)
  Dual-Pull ._◁_ p v = v ▷ p
  Dual-Pull ⦃ pp ⦄ .pull-refl = pp .Push.push-refl

{-# INCOHERENT Dual-Refl Dual-Sym Dual-Reflᵈ Dual-Push Dual-Pull #-}
