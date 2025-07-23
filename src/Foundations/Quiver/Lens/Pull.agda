{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull where

open import Foundations.Quiver.Base

open import Notation.Pull
open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  (α⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls))
  ⦃ _ : Refl C ⦄ where
  private module α⁻ {ls} t = Quiver-onω (α⁻ {ls} t) renaming (Het to Hom)

  Disp⁻ : ⦃ _ : HPull C k α⁻ ⦄ → HQuiver-onωᵈ C k F _
  Disp⁻ .Quiver-onωᵈ.Het[_] {x} p u v = α⁻.Hom x (pull p v) u

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {α⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ where instance

  Disp⁻-Reflᵈ : ⦃ _ : HPull C k α⁻ ⦄ → Reflᵈ (Disp⁻ α⁻)
  Disp⁻-Reflᵈ .reflᵈ = pull-refl
  {-# INCOHERENT Disp⁻-Reflᵈ #-} -- TODO check
