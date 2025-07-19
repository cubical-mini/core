{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Pull where

open import Foundations.Quiver.Base

open import Notation.Pull
open import Notation.Refl

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {n} {ℓ-obᶠ : Levels m → ℓ-sig n} {ℓ-homᶠ : Levels m → ℓ-sig² n n}
  {Ob[_]⁻ Ob[_]⁺ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  (F⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω n Ob[ t ]⁻ (ℓ-homᶠ ls)) where
  private module F⁻ {ls} t = Quiver-onω (F⁻ {ls} t)

  Disp⁻ : ⦃ _ : Pullω C n Ob[_]⁻ Ob[_]⁺ ⦄ → Quiver-onωᵈ Ob Ob Hom n n Ob[_]⁻ Ob[_]⁺ _
  Disp⁻ .Quiver-onωᵈ.Het[_] {x} p u v = F⁻.Het x (pull p v) u

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {n} {ℓ-obᶠ : Levels m → ℓ-sig n} {ℓ-homᶠ : Levels m → ℓ-sig² n n}
  {Ob[_] : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {F⁻ : ∀{ls} (t : Ob ls) → HQuiver-onω n Ob[ t ] (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

  Disp⁻-Reflᵈ : ⦃ _ : Pullω C n Ob[_] Ob[_] ⦄ ⦃ _ : Lawful-Pullω C F⁻ ⦄ → Reflωᵈ C (Disp⁻ C F⁻)
  Disp⁻-Reflᵈ .reflᵈ _ = pull-refl
  {-# INCOHERENT Disp⁻-Reflᵈ #-} -- TODO check
