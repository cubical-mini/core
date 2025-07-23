{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Profunctor where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual

open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} (let module A = Quiver-onω A renaming (Het to Hom))
  {B : HQuiver-onω n Ob⁺ ℓ-hom⁺} (let module B = Quiver-onω B renaming (Het to Hom))
  {k} {ℓ-hetᶠ ℓ-hetᵍ : ℓ-sig 3 (m , n , k , _)}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  {ℓ-het : ℓ-sig 4 (m , n , k , k , _)}
  {α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-het lxs lys)}
  ⦃ _ : Refl A ⦄ ⦃ _ : Refl B ⦄ ⦃ _ : Profunctor A B k α ⦄ where instance

  Profunctor→Pull : ∀{lys} {y : Ob⁺ lys} → Pull A k (λ x → α x y ᵒᵖ)
  Profunctor→Pull .pull p = dimap p refl
  Profunctor→Pull .pull-refl = dimap-refl

  Profunctor→Push : ∀{lxs} {x : Ob⁻ lxs} → Push B k (λ y → α x y)
  Profunctor→Push .push = dimap refl
  Profunctor→Push .push-refl = dimap-refl

-- TODO check
{-# INCOHERENT Profunctor→Pull Profunctor→Push #-}
