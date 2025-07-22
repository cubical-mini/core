{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Profunctor where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual

open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

-- TODO can we just use push instances?

module _ {ma ℓ-oba⁻} {Oba⁻ : ob-sig ℓ-oba⁻} {na ℓ-oba⁺} {Oba⁺ : ob-sig ℓ-oba⁺}
  {ℓ-heta⁻} {A : Quiver-onω ma Oba⁻ na Oba⁺ ℓ-heta⁻}
  {mb ℓ-obb} {Obb : ob-sig ℓ-obb} {ℓ-homb⁻}
  {B : HQuiver-onω mb Obb ℓ-homb⁻}
  {k} {ℓ-hetᶠ : ℓ-sig 3 (na , mb , k , _)} {ℓ-hetᵍ : ℓ-sig 3 (ma , mb , k , _)}
  {F : ob-sigᵈ² Oba⁺ Obb ℓ-hetᶠ} {G : ob-sigᵈ² Oba⁻ Obb ℓ-hetᵍ}
  ⦃ _ : Profunctorω A B k F G ⦄ ⦃ _ : Reflω B ⦄ {lys} {y : Obb lys} where instance

  Profunctor→Pull : Pullω A k (λ x → G x y) (λ x → F x y)
  Profunctor→Pull .pull p v = dimap p refl v

module _ {ma ℓ-oba} {Oba : ob-sig ℓ-oba} {ℓ-homa}
  {A : HQuiver-onω ma Oba ℓ-homa}
  {mb ℓ-obb⁻} {Obb⁻ : ob-sig ℓ-obb⁻} {nb ℓ-obb⁺} {Obb⁺ : ob-sig ℓ-obb⁺}
  {ℓ-hetb⁻} {B : Quiver-onω mb Obb⁻ nb Obb⁺ ℓ-hetb⁻}
  {k} {ℓ-hetᶠ : ℓ-sig 3 (ma , mb , k , _)} {ℓ-hetᵍ : ℓ-sig 3 (ma , nb , k , _)}
  {F : ob-sigᵈ² Oba Obb⁻ ℓ-hetᶠ} {G : ob-sigᵈ² Oba Obb⁺ ℓ-hetᵍ}
  ⦃ _ : Profunctorω A B k F G ⦄ ⦃ _ : Reflω A ⦄ {lxs} {x : Oba lxs} where instance

  Profunctor→Push : Pushω B k (λ y → F x y) (λ y → G x y)
  Profunctor→Push .push p u = dimap refl p u


module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-hom⁻ ℓ-hom⁺}
  {Ob⁻ : ob-sig ℓ-ob⁻} {Ob⁺ : ob-sig ℓ-ob⁺}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} (let module A = Quiver-onω A renaming (Het to Hom))
  {B : HQuiver-onω n Ob⁺ ℓ-hom⁺} (let module B = Quiver-onω B renaming (Het to Hom))
  {k} {ℓ-hetᶠ ℓ-hetᵍ : ℓ-sig 3 (m , n , k , _)}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  ⦃ sp : SProfunctorω A B k F G ⦄ where

  module _ ⦃ _ : Reflω B ⦄ {lys} {y : Ob⁺ lys} where instance
    Lawful-Profunctor→Pull : {ℓ-hetʰ : ℓ-sig 4 (m , n , k , k , _)}
                             {α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (G x y) k (F x y) (ℓ-hetʰ lxs lys)}
                             ⦃ ra : Reflω A ⦄ ⦃ lp : Lawful-Profunctorω A B λ x y → α x y ᵒᵖ ⦄
                           → Lawful-Pullω A (λ x → α x y) ⦃ auto ⦄ ⦃ Profunctor→Pull ⦃ sp ⦄ ⦄
    Lawful-Profunctor→Pull .pull-refl = dimap-refl

  module _ ⦃ _ : Reflω A ⦄ {lxs} {x : Ob⁻ lxs} where instance
    Lawful-Profunctor→Push : {ℓ-hetʰ : ℓ-sig 4 (m , n , k , k , _)}
                             {α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-hetʰ lxs lys)}
                             ⦃ _ : Reflω B ⦄ ⦃ _ : Lawful-Profunctorω A B α ⦄
                           → Lawful-Pushω B (λ y → α x y) ⦃ auto ⦄ ⦃ Profunctor→Push ⦃ sp ⦄ ⦄
    Lawful-Profunctor→Push .push-refl = dimap-refl

-- TODO check
{-# INCOHERENT
  Profunctor→Pull Profunctor→Push
  Lawful-Profunctor→Pull Lawful-Profunctor→Push
#-}
