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
  {k ℓ-obᶠ⁻ ℓ-obᶠ⁺} {Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᶠ⁻} {Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᶠ⁺}
  where instance

  Dual-Push : ⦃ _ : Pullω C k Ob[_]⁻ Ob[_]⁺ ⦄ → Pushω (Op C) k Ob[_]⁺ Ob[_]⁻
  Dual-Push .push = pull

  Dual-Pull : ⦃ _ : Pushω C k Ob[_]⁻ Ob[_]⁺ ⦄ → Pullω (Op C) k Ob[_]⁺ Ob[_]⁻
  Dual-Pull .pull = push


module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} {C : HQuiver-onω m Ob ℓ-hom}
  {k ℓ-obᶠ⁻ ℓ-obᶠ⁺} {Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᶠ⁻} {Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᶠ⁺}
  {ℓ-hetᶠ : ℓ-sig 3 (m , k , k , _)}
  {F : ∀{ls} (t : Ob ls) → Quiver-onω k Ob[ t ]⁻ k Ob[ t ]⁺ (ℓ-hetᶠ ls)}
  ⦃ _ : Reflω C ⦄ where instance

    Dual-Push-Lawful : ⦃ _ : SPullω C k Ob[_]⁻ Ob[_]⁺ ⦄ ⦃ lp : Lawful-Pullω C F ⦄
                     → Lawful-Pushω (Op C) (λ t → Op (F t))
    Dual-Push-Lawful ⦃ lp ⦄ .push-refl = lp .Lawful-Pull.pull-refl

    Dual-Pull-Lawful : ⦃ _ : SPushω C k Ob[_]⁻ Ob[_]⁺ ⦄ ⦃ lp : Lawful-Pushω C F ⦄
                     → Lawful-Pullω (Op C) (λ t → Op (F t))
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
  {H : ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → Quiver-onω k (F x y) k (G x y) (ℓ-hetʰ lxs lys)}
  ⦃ _ : Reflω A ⦄ ⦃ _ : Reflω B ⦄ ⦃ _ : SProfunctorω A B k F G ⦄ where instance

  Dual-Profunctor-Lawful : ⦃ lp : Lawful-Profunctorω A B H ⦄ → Lawful-Profunctorω (Op B) (Op A) (λ y x → H x y)
  Dual-Profunctor-Lawful ⦃ lp ⦄ .dimap-refl = lp .Lawful-Profunctor.dimap-refl

-- TODO check pragmas
{-# INCOHERENT
  Dual-Push Dual-Pull
  Dual-Push-Lawful Dual-Pull-Lawful
  Dual-Profunctor
  Dual-Profunctor-Lawful
#-}
