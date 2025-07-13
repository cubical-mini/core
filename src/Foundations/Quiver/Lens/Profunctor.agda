{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Profunctor where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual

open import Notation.Lens.Profunctor
open import Notation.Lens.Pull
open import Notation.Lens.Push
open import Notation.Refl

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} (let module A = Quiver-onω A renaming (Het to Hom))
  {B : HQuiver-onω n Ob⁺ ℓ-hom⁺} (let module B = Quiver-onω B renaming (Het to Hom))
  {k} {ℓ-hetᶠ ℓ-hetᵍ : Levels m → Levels n → ℓ-sig k}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ} where

  module _ ⦃ _ : Profunctorω A B k F G ⦄ ⦃ _ : Reflω B ⦄ where instance
    Profunctor→Pull : ∀{lys} {y : Ob⁺ lys} → Pullω A k (λ x → G x y) (λ x → F x y)
    Profunctor→Pull .pull p v = p ◁ v

    Lawful-Profunctor→Pull : ∀ {ℓ-hetʰ : Levels m → Levels n → ℓ-sig² k k}
                             {H : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k k (G x y) (F x y) (ℓ-hetʰ lxs lys)}
                             ⦃ _ : Reflω A ⦄ ⦃ _ : Lawful-Profunctorω A B λ x y → Op (H x y) ⦄
                             {lys} {y : Ob⁺ lys}
                           → Lawful-Pullω A (λ x → H x y)
    Lawful-Profunctor→Pull .pull-refl = dimap-refl

  module _ ⦃ _ : Profunctorω A B k F G ⦄ ⦃ _ : Reflω A ⦄ where instance
    Profunctor→Push : ∀{lxs} {x : Ob⁻ lxs} → Pushω B k (λ y → F x y) (λ y → G x y)
    Profunctor→Push .push p u = u ▷ p

    Lawful-Profunctor→Push : ∀ {ℓ-hetʰ : Levels m → Levels n → ℓ-sig² k k}
                             {H : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k k (F x y) (G x y) (ℓ-hetʰ lxs lys)}
                             ⦃ _ : Reflω B ⦄ ⦃ _ : Lawful-Profunctorω A B H ⦄
                             {lxs} {x : Ob⁻ lxs}
                           → Lawful-Pushω B (λ y → H x y)
    Lawful-Profunctor→Push .push-refl = dimap-refl
