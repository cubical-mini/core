{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull where

open import Foundations.Quiver.Base

open import Notation.Pull
open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {F G : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  (α⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)) where
  private module α⁻ {ls} t = Quiver-onω (α⁻ {ls} t) renaming (Het to Hom)

  Disp⁻ : ⦃ _ : SPullω C k F G ⦄ → SQuiver-onωᵈ C k F k G _
  Disp⁻ .Quiver-onωᵈ.Het[_] {x} p u v = α⁻.Hom x (pull p v) u

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {α⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

  Disp⁻-Reflᵈ : ⦃ _ : HPullω C k F ⦄ ⦃ _ : Lawful-Pullω C α⁻ ⦄ → Reflωᵈ (Disp⁻ C α⁻)
  Disp⁻-Reflᵈ .reflᵈ = pull-refl
  {-# INCOHERENT Disp⁻-Reflᵈ #-} -- TODO check
