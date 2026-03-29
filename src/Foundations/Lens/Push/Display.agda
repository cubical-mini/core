module Foundations.Lens.Push.Display where

open import Foundations.Base
open import Foundations.Lens.Push.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  (α⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)) where
  private module α⁺ {ls} t = Quiver-onω (α⁺ {ls} t) renaming (Het to Hom)

  Disp⁺ : ⦃ _ : Refl C ⦄ ⦃ _ : HPush C k α⁺ ⦄ → HQuiver-onωᵈ C k F _
  Disp⁺ .Quiver-onωᵈ.Het[_] {y} p u v = α⁺.Hom y (u ▷ p) v

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {α⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)} where instance

  Disp⁺-Reflᵈ : ⦃ _ : Refl C ⦄ ⦃ _ : HPush C k α⁺ ⦄ → Reflᵈ (Disp⁺ α⁺)
  Disp⁺-Reflᵈ .reflᵈ = push-refl
  {-# INCOHERENT Disp⁺-Reflᵈ #-} -- TODO check
