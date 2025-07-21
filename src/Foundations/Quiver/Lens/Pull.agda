{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull where

open import Foundations.Quiver.Base

open import Notation.Pull
open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {Ob[_]⁻ Ob[_]⁺ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  (F⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k Ob[ t ]⁻ (ℓ-homᶠ ls)) where
  private module F⁻ {ls} t = Quiver-onω (F⁻ {ls} t) renaming (Het to Hom)

  Disp⁻ : ⦃ _ : SPullω C k Ob[_]⁻ Ob[_]⁺ ⦄ → SQuiver-onωᵈ Ob Hom k Ob[_]⁻ k Ob[_]⁺ _
  Disp⁻ .Quiver-onωᵈ.Het[_] {x} p u v = F⁻.Hom x (pull p v) u

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {Ob[_] : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {F⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω k Ob[ t ] (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

  Disp⁻-Reflᵈ : ⦃ _ : HPullω C k Ob[_] ⦄ ⦃ _ : Lawful-Pullω C F⁻ ⦄ → Reflωᵈ C (Disp⁻ C F⁻)
  Disp⁻-Reflᵈ .reflᵈ _ = pull-refl
  {-# INCOHERENT Disp⁻-Reflᵈ #-} -- TODO check
