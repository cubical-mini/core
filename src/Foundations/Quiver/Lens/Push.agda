{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Push where

open import Foundations.Quiver.Base

open import Notation.Push
open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {Ob[_]⁻ Ob[_]⁺ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  (F⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω k Ob[ t ]⁺ (ℓ-homᶠ ls)) where
  private module F⁺ {ls} t = Quiver-onω (F⁺ {ls} t) renaming (Het to Hom)

  Disp⁺ : ⦃ _ : SPushω C k Ob[_]⁻ Ob[_]⁺ ⦄ → SQuiver-onωᵈ Ob Hom k Ob[_]⁻ k Ob[_]⁺ _
  Disp⁺ .Quiver-onωᵈ.Het[_] {y} p u v = F⁺.Hom y v (push p u)

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ : ℓ-sig 2 (m , k , _)} {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {Ob[_] : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ ls)}
  {F⁺ : ∀{ls} (t : Ob ls) → HQuiver-onω k Ob[ t ] (ℓ-homᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

  Disp⁺-Reflᵈ : ⦃ _ : HPushω C k Ob[_] ⦄ ⦃ _ : Lawful-Pushω C F⁺ ⦄ → Reflωᵈ C (Disp⁺ C F⁺)
  Disp⁺-Reflᵈ .reflᵈ _ = push-refl
  {-# INCOHERENT Disp⁺-Reflᵈ #-} -- TODO check
