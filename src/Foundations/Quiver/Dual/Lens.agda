{-# OPTIONS --safe #-}
module Foundations.Quiver.Dual.Lens where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Dual.Base
open import Foundations.Quiver.Dual.Groupoid

open import Notation.Profunctor
open import Notation.Pull
open import Notation.Push
open import Notation.Refl

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  {C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het}
  {k ℓ-obᶠ ℓ-obᵍ} {F : ob-sigᵈ Ob⁻ ℓ-obᶠ} {G : ob-sigᵈ Ob⁺ ℓ-obᵍ}
  where instance

  Dual-Push : ⦃ _ : Pullω C k F G ⦄ → Pushω (Op C) k G F
  Dual-Push .push = pull

  Dual-Pull : ⦃ _ : Pushω C k F G ⦄ → Pullω (Op C) k G F
  Dual-Pull .pull = push


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {k ℓ-obᶠ ℓ-obᵍ} {F : ob-sigᵈ Ob ℓ-obᶠ} {G : ob-sigᵈ Ob ℓ-obᵍ}
  {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → Quiver-onω k (F t) k (G t) (ℓ-hetᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

    Dual-Push-Lawful : ⦃ _ : SPullω C k F G ⦄ ⦃ lp : Lawful-Pullω C α ⦄
                     → Lawful-Pushω (Op C) (λ t → Op (α t))
    Dual-Push-Lawful ⦃ lp ⦄ .push-refl = lp .Lawful-Pull.pull-refl

    Dual-Pull-Lawful : ⦃ _ : SPushω C k F G ⦄ ⦃ lp : Lawful-Pushω C α ⦄
                     → Lawful-Pullω (Op C) (λ t → Op (α t))
    Dual-Pull-Lawful ⦃ lp ⦄ .pull-refl = lp .Lawful-Push.push-refl


module _ {ma ℓ-oba⁻} {Oba⁻ : ob-sig ℓ-oba⁻} {na ℓ-oba⁺} {Oba⁺ : ob-sig ℓ-oba⁺}
  {ℓ-heta⁻} {A : Quiver-onω ma Oba⁻ na Oba⁺ ℓ-heta⁻}
  {mb ℓ-obb⁻} {Obb⁻ : ob-sig ℓ-obb⁻} {nb ℓ-obb⁺} {Obb⁺ : ob-sig ℓ-obb⁺}
  {ℓ-hetb⁻} {B : Quiver-onω mb Obb⁻ nb Obb⁺ ℓ-hetb⁻}
  {k} {ℓ-hetᶠ : ℓ-sig 3 (na , mb , k , _)} {ℓ-hetᵍ : ℓ-sig 3 (ma , nb , k , _)}
  {F : ob-sigᵈ² Oba⁺ Obb⁻ ℓ-hetᶠ} {G : ob-sigᵈ² Oba⁻ Obb⁺ ℓ-hetᵍ} where instance

  Dual-Profunctor : ⦃ pr : Profunctorω A B k F G ⦄
                  → Profunctorω (Op B) (Op A) k (λ y x → F x y) (λ y x → G x y)
  Dual-Profunctor .dimap p q = dimap q p


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-hom⁻ ℓ-hom⁺}
  {A : HQuiver-onω m Ob⁻ ℓ-hom⁻} {B : HQuiver-onω n Ob⁺ ℓ-hom⁺}
  {k} {ℓ-hetᶠ ℓ-hetᵍ : ℓ-sig 3 (m , n , k , _)}
  {F : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᶠ} {G : ob-sigᵈ² Ob⁻ Ob⁺ ℓ-hetᵍ}
  {ℓ-hetʰ : ℓ-sig 4 (m , n , k , k , _)}
  {α : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-hetʰ lxs lys)}
  ⦃ _ : Reflω A ⦄ ⦃ _ : Reflω B ⦄ ⦃ _ : SProfunctorω A B k F G ⦄ where instance

  Dual-Profunctor-Lawful : ⦃ lp : Lawful-Profunctorω A B α ⦄ → Lawful-Profunctorω (Op B) (Op A) (λ y x → α x y)
  Dual-Profunctor-Lawful ⦃ lp ⦄ .dimap-refl = lp .Lawful-Profunctor.dimap-refl

-- TODO check pragmas
{-# INCOHERENT
  Dual-Push Dual-Pull
  Dual-Push-Lawful Dual-Pull-Lawful
  Dual-Profunctor
  Dual-Profunctor-Lawful
#-}
